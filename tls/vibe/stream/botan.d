/**
	Botan TLS implementation
	Copyright: © 2015 Sönke Ludwig, GlobecSys Inc
	Authors: Sönke Ludwig, Etienne Cimon
	License: Subject to the terms of the MIT license, as written in the included LICENSE.txt file.
*/
module vibe.stream.botan;

version (VibeNoSSL) {}
else version(Have_botan):

version = X509;
import botan.constants;
import botan.cert.x509.x509cert;
import botan.cert.x509.certstor;
import botan.cert.x509.x509path;
import botan.math.bigint.bigint;
import botan.tls.blocking;
import memutils.unreadring;
static assert(__traits(hasMember, TLSBlockingChannel, "unreadPut"));
static assert(__traits(hasMember, TLSBlockingChannel, "unreadDrainRecv"));
static assert(__traits(hasMember, TLSBlockingChannel, "unreadOnTCP"));
import botan.tls.channel;
import botan.tls.credentials_manager;
import botan.tls.exceptn;
import botan.tls.server;
import botan.tls.session_manager;
import botan.tls.server_info;
import botan.tls.ciphersuite;
import botan.tls.policy;
import botan.tls.version_;
import botan.rng.auto_rng;
import botan.rng.rng;
import botan.algo_base.symkey : SymmetricKey;

/// HMAC_RNG reseeds from every entropy source every 512 bytes
/// (callgrind: mutex + poll dominate ECDSA reconnect). ChaCha_RNG
/// seeded once is enough for a single-threaded TLS event loop.
private RandomNumberGenerator makeTlsRng()
{
	static if (BOTAN_HAS_CHACHA_RNG)
	{
		import botan.rng.chacha_rng : ChaChaRNG;
		auto seed = new AutoSeededRNG();
		auto b = seed.randomVec(48);
		auto cr = new ChaChaRNG(b.ptr, b.length);
		cr.unlockForSingleThread();
		return cr;
	}
	else
		return new AutoSeededRNG();
}
import vibe.core.stream;
import vibe.stream.tls;
import vibe.core.net;
import vibe.internal.interfaceproxy : InterfaceProxy;
import std.datetime;
import std.exception;

class BotanTLSStream : TLSStream/*, Buffered*/
{
	@safe:

	private {
		InterfaceProxy!Stream m_stream;
		TLSBlockingChannel m_tlsChannel;
		BotanTLSContext m_ctx;

		OnAlert m_alertCB;
		OnHandshakeComplete m_handshakeComplete;
		TLSCiphersuite m_cipher;
		TLSProtocolVersion m_ver;
		SysTime m_session_age;
		X509Certificate m_peer_cert;
		TLSCertificateInformation m_cert_compat;
		ubyte[] m_sess_id;
		Exception m_ex;
		// Coalesce HTTP header+body into one TLS record (16 KiB is the
		// TLS 1.2 plaintext ceiling). vibe.0 BotanTLSStream does the
		// same; without it writeHeader + writeBody each call send().
		enum size_t outCap = 16 * 1024;
		ubyte[] m_outBuf;
		// Ciphertext records from onWrite. Handshake emits SH+CCS+EE+
		// Cert+CV+Finished as separate records; one TCP write per
		// record was 6 fiber yields per ECDSA reconnect.
		ubyte[] m_recBuf;
	}

	/// Returns the date/time the session was started
	@property SysTime started() const { return m_session_age; }

	/// Get the session ID
	@property const(ubyte[]) sessionId() { return m_sess_id; }

	/// Returns the remote public certificate from the chain
	@property const(X509Certificate) x509Certificate() const @system { return m_peer_cert; }

	/// Returns the negotiated version of the TLS Protocol
	@property TLSProtocolVersion protocol() const { return m_ver; }

	/// Returns the complete ciphersuite details from the negotiated TLS connection
	@property TLSCiphersuite cipher() const { return m_cipher; }

	@property string alpn() const @trusted { return m_tlsChannel.underlyingChannel().applicationProtocol(); }

	@property TLSCertificateInformation peerCertificate()
	{
		import vibe.core.log : logWarn;

		if (!!m_peer_cert)
			logWarn("BotanTLSStream.peerCertificate is not implemented and does not return the actual certificate information.");

		return TLSCertificateInformation.init;
	}

	// Constructs a new TLS Client Stream and connects with the specified handlers
	this(InterfaceProxy!Stream underlying, BotanTLSContext ctx,
		 void delegate(in TLSAlert alert, in ubyte[] ub) alert_cb,
		 bool delegate(in TLSSession session) hs_cb,
		 string peer_name = null, NetworkAddress peer_address = NetworkAddress.init)
	@trusted {
		m_ctx = ctx;
		m_stream = underlying;
		m_alertCB = alert_cb;
		m_handshakeComplete = hs_cb;

		assert(m_ctx.m_kind == TLSContextKind.client, "Connecting through a server context is not supported");
		// todo: add service name?
		ushort pport = 443;
		if (peer_address.family)
			pport = peer_address.port;
		TLSServerInformation server_info = TLSServerInformation(peer_name, pport);
		m_tlsChannel = TLSBlockingChannel(&onRead, &onWrite,  &onAlert, &onHandhsakeComplete, m_ctx.m_sessionManager, m_ctx.m_credentials, m_ctx.m_policy, m_ctx.m_rng, server_info, m_ctx.m_offer_version, m_ctx.m_clientOffers.clone);

		try m_tlsChannel.doHandshake();
		catch (Exception e) {
			m_ex = e;
		}
		flushRec();
	}

	// This constructor is used by the TLS Context for both server and client streams
	this(InterfaceProxy!Stream underlying, BotanTLSContext ctx, TLSStreamState state, string peer_name = null, NetworkAddress peer_address = NetworkAddress.init)
	@trusted {
		m_ctx = ctx;
		m_stream = underlying;

		if (state == TLSStreamState.accepting)
		{
			assert(m_ctx.m_kind != TLSContextKind.client, "Accepting through a client context is not supported");
			m_tlsChannel = TLSBlockingChannel(&onRead, &onWrite, &onAlert, &onHandhsakeComplete, m_ctx.m_sessionManager, m_ctx.m_credentials, m_ctx.m_policy, m_ctx.m_rng, &m_ctx.nextProtocolHandler, &m_ctx.sniHandler, m_ctx.m_is_datagram);

		}
		else if (state == TLSStreamState.connecting) {
			assert(m_ctx.m_kind == TLSContextKind.client, "Connecting through a server context is not supported");
			// todo: add service name?
			ushort pport = 443;
			if (peer_address.family)
				pport = peer_address.port;
			TLSServerInformation server_info = TLSServerInformation(peer_name, pport);
			m_tlsChannel = TLSBlockingChannel(&onRead, &onWrite,  &onAlert, &onHandhsakeComplete, m_ctx.m_sessionManager, m_ctx.m_credentials, m_ctx.m_policy, m_ctx.m_rng, server_info, m_ctx.m_offer_version, m_ctx.m_clientOffers.clone);
		}
		else /*if (state == TLSStreamState.connected)*/ {
			m_tlsChannel = TLSBlockingChannel.init;
			throw new Exception("Cannot load BotanTLSSteam from a connected TLS session");
		}

		try m_tlsChannel.doHandshake();
		catch (Exception e) {
			m_ex = e;
		}
		flushRec();
	}

	~this()
	@trusted {
		try m_tlsChannel.destroy();
		catch (Exception e) {
		}
	}

	void flush()
	{
		processException();
		flushOut();
		flushRec();
		m_stream.flush();
	}

	void finalize()
	{
		if (() @trusted { return m_tlsChannel.isClosed(); } ())
			return;

		processException();
		scope(success)
			processException();

		flushOut();
		() @trusted { m_tlsChannel.close(); } ();
		flushRec();
		m_stream.flush();
	}

	size_t read(scope ubyte[] dst, IOMode mode)
	{
		processException();
		scope(success)
			processException();
		// HTTP client GET writes headers then reads the response
		// without flush(); OpenSSL SSL_write hid that. Push the
		// coalesced record before we block on plaintext.
		flushOut();
		if (!dst.length) return 0;
		// Same contract as OpenSSLTLSStream: once/immediate return a
		// partial plaintext fill; all waits for dst.length.
		if (mode == IOMode.immediate && !dataAvailableForRead)
			return 0;
		if (mode == IOMode.once || mode == IOMode.immediate) {
			auto got = () @trusted { return m_tlsChannel.readBuf(dst); } ();
			return got.length;
		}
		() @trusted { m_tlsChannel.read(dst); } ();
		return dst.length;
	}

	alias read = Stream.read;

	ubyte[] readChunk(ubyte[] buf)
	{
		processException();
		scope(success)
			processException();
		return () @trusted { return m_tlsChannel.readBuf(buf); } ();
	}

	size_t write(scope const(ubyte)[] bytes, IOMode)
	{
		processException();
		scope(success)
			processException();
		if (!bytes.length) return 0;
		if (m_outBuf.length && m_outBuf.length + bytes.length > outCap)
			flushOut();
		if (bytes.length >= outCap)
			() @trusted { m_tlsChannel.write(bytes); } ();
		else
			appendOut(bytes);
		return bytes.length;
	}

	alias write = Stream.write;

	@property bool empty()
	{
		processException();
		return leastSize() == 0;
	}

	@property ulong leastSize()
	{
		flushOut();
		size_t ret = () @trusted { return m_tlsChannel.pending(); } ();
		if (ret > 0) return ret;
		if (() @trusted { return m_tlsChannel.isClosed(); } () || m_ex !is null) return 0;
		try () @trusted { m_tlsChannel.readBuf(null); } (); // force an exchange
		catch (Exception e) { return 0; }
		ret = () @trusted { return m_tlsChannel.pending(); } ();
		//logDebug("Least size returned: ", ret);
		return ret > 0 ? ret : m_stream.empty ? 0 : 1;
	}

	@property bool dataAvailableForRead()
	{
		processException();
		// Match OpenSSLTLSStream: plaintext already decrypted, or the
		// TCP leftover ring still holds a record. Do not decrypt here —
		// HTTP keep-alive only needs a non-blocking yes/no.
		return () @trusted { return m_tlsChannel.pending(); } () > 0
			|| m_stream.dataAvailableForRead;
	}

	const(ubyte)[] peek()
	{
		processException();
		auto peeked = () @trusted { return m_tlsChannel.peek(); } ();
		//logDebug("Peeked data: ", cast(ubyte[])peeked);
		//logDebug("Peeked data ptr: ", peeked.ptr);
		return peeked;
	}

	void setAlertCallback(OnAlert alert_cb)
	@system {
		processException();
		m_alertCB = alert_cb;
	}

	void setHandshakeCallback(OnHandshakeComplete hs_cb)
	@system {
		processException();
		m_handshakeComplete = hs_cb;
	}

	private void appendOut(scope const(ubyte)[] bytes)
	@trusted {
		if (!m_outBuf.capacity)
			m_outBuf.reserve(outCap);
		m_outBuf ~= bytes;
	}

	private void flushOut()
	@trusted {
		if (!m_outBuf.length) return;
		m_tlsChannel.write(m_outBuf);
		m_outBuf.length = 0;
		m_outBuf.assumeSafeAppend();
		flushRec();
	}

	private void flushRec()
	@trusted {
		if (!m_recBuf.length) return;
		try m_stream.write(m_recBuf);
		catch (Exception e) {
			import std.algorithm : canFind;
			if (e.msg.canFind("Connection closed") || e.msg.canFind("end of stream"))
			{
				m_recBuf.length = 0;
				return;
			}
			if (m_ex is null)
				m_ex = e;
		}
		m_recBuf.length = 0;
		m_recBuf.assumeSafeAppend();
	}

	private void processException()
	@safe {
		if (auto ex = m_ex) {
			m_ex = null;
			throw ex;
		}
	}

	private void onAlert(in TLSAlert alert, in ubyte[] data)
	@trusted {
		if (alert.isFatal)
			m_ex = new Exception("TLS Alert Received: " ~ alert.typeString());
		if (m_alertCB)
			m_alertCB(alert, data);
	}

	private bool onHandhsakeComplete(in TLSSession session)
	@trusted {
		m_sess_id = cast(ubyte[])session.sessionId()[].dup;
		m_cipher = session.ciphersuite();
		m_session_age = session.startTime();
		m_ver = session.Version();
		if (session.peerCerts().length > 0)
			m_peer_cert = session.peerCerts()[0];
		if (m_handshakeComplete)
			return m_handshakeComplete(session);
		return true;
	}

	private ubyte[] onRead(ubyte[] buf)
	{
		import std.algorithm : min;

		flushRec();
		if (!buf.length) return null;
		// Prefer the TCP leftover already in vibe-core's read buffer
		// (peek) so keep-alive does not wait. leastSize() waits.
		size_t avail = m_stream.peek().length;
		if (!avail)
			avail = cast(size_t) m_stream.leastSize();
		size_t len = min(avail, buf.length);
		if (len == 0) return null;
		m_stream.read(buf[0 .. len]);
		return buf[0 .. len];
	}

	private void onWrite(in ubyte[] src) {
		if (!src.length) return;
		if (m_recBuf.length && m_recBuf.length + src.length > outCap)
			flushRec();
		if (src.length >= outCap) {
			flushRec();
			try m_stream.write(src);
			catch (Exception e) {
				import std.algorithm : canFind;
				if (e.msg.canFind("Connection closed") || e.msg.canFind("end of stream"))
					return;
				if (m_ex is null)
					m_ex = e;
			}
			return;
		}
		if (!m_recBuf.capacity)
			m_recBuf.reserve(outCap);
		m_recBuf ~= src;
	}
}

class BotanTLSContext : TLSContext {
	private {
		TLSSessionManager m_sessionManager;
		TLSPolicy m_policy;
		TLSCredentialsManager m_credentials;
		TLSContextKind m_kind;
		RandomNumberGenerator m_rng;
		TLSProtocolVersion m_offer_version;
		TLSServerNameCallback m_sniCallback;
		TLSALPNCallback m_serverCb;
		Vector!string m_clientOffers;
		bool m_is_datagram;
		bool m_certChecked;
	}

	this(TLSContextKind kind,
		 TLSCredentialsManager credentials = null,
		 TLSPolicy policy = null,
		 TLSSessionManager session_manager = null,
		 bool is_datagram = false)
	@trusted {
		this(kind, TLSVersion.any, credentials, policy, session_manager, is_datagram);
	}

	/// Applies `ver` to a CustomTLSPolicy (min/offer/max) and the
	/// client offer. `any` / `tls1_2` match OpenSSL: min 1.2, max 1.3
	/// when TLS 1.3 is compiled. botan `latestTlsVersion()` stays 1.2.
	/// `tls1_3` is 1.3-only.
	this(TLSContextKind kind, TLSVersion ver,
		 TLSCredentialsManager credentials = null,
		 TLSPolicy policy = null,
		 TLSSessionManager session_manager = null,
		 bool is_datagram = false)
	@trusted {
		const bool default_creds = credentials is null;
		if (!credentials)
			credentials = new CustomTLSCredentials();
		m_kind = kind;
		m_credentials = credentials;
		m_is_datagram = is_datagram || ver == TLSVersion.dtls1;

		m_rng = makeTlsRng();
		if (!session_manager)
			session_manager = new TLSSessionManagerInMemory(m_rng);
		m_sessionManager = session_manager;

		if (!policy) {
			if (ver == TLSVersion.any && !m_is_datagram) {
				if (!gs_default_policy) {
					gs_default_policy = new CustomTLSPolicy();
					gs_default_policy.applyTlsVersion(TLSVersion.any);
				}
				policy = cast(TLSPolicy)gs_default_policy;
			} else {
				auto dedicated = new CustomTLSPolicy();
				dedicated.applyTlsVersion(ver);
				policy = dedicated;
			}
		} else if (auto custom = cast(CustomTLSPolicy) policy) {
			if (ver != TLSVersion.any)
				custom.applyTlsVersion(ver);
		}
		m_policy = policy;
		applyProtocolOffer(ver);

		if (default_creds && m_kind == TLSContextKind.client)
			peerValidationMode = TLSPeerValidationMode.trustedCert;
	}

	private void applyProtocolOffer(TLSVersion ver)
	@trusted {
		if (auto custom = cast(CustomTLSPolicy) m_policy) {
			if (custom.offerProtocolVersion.valid)
				m_offer_version = custom.offerProtocolVersion;
			else
				m_offer_version = m_policy.latestSupportedVersion(m_is_datagram);
			return;
		}
		if (ver == TLSVersion.tls1_3)
			m_offer_version = TLSProtocolVersion(TLSProtocolVersion.TLS_V13);
		else if (ver == TLSVersion.dtls1 || m_is_datagram)
			m_offer_version = m_policy.latestSupportedVersion(true);
		else
			m_offer_version = m_policy.latestSupportedVersion(false);
	}

	/// The kind of TLS context (client/server)
	@property TLSContextKind kind() const {
		return m_kind;
	}

	/// Used by clients to indicate protocol preference, use TLSPolicy to restrict the protocol versions
	@property void defaultProtocolOffer(TLSProtocolVersion ver) { m_offer_version = ver; }
	/// ditto
	@property TLSProtocolVersion defaultProtocolOffer() { return m_offer_version; }

	/// Cap the CustomTLSPolicy max (e.g. force 1.2 when the cert is ECDSA —
	/// Botan TLS 1.3 CertificateVerify is still RSA-PSS only).
	@property void maxProtocolVersion(TLSProtocolVersion ver)
	{
		if (auto p = cast(CustomTLSPolicy) m_policy)
			p.maxProtocolVersion = ver;
	}
	/// ditto
	@property TLSProtocolVersion maxProtocolVersion()
	{
		if (auto p = cast(CustomTLSPolicy) m_policy)
			return p.maxProtocolVersion;
		return TLSProtocolVersion.init;
	}

	@property void sniCallback(TLSServerNameCallback callback)
	{
		m_sniCallback = callback;
	}
	@property inout(TLSServerNameCallback) sniCallback() inout { return m_sniCallback; }

	/// Callback function invoked by server to choose alpn
	@property void alpnCallback(TLSALPNCallback alpn_chooser)
	{
		m_serverCb = alpn_chooser;
	}

	/// Get the current ALPN callback function
	@property TLSALPNCallback alpnCallback() const { return m_serverCb; }

	/// Invoked by client to offer alpn, all strings are copied on the GC
	@property void setClientALPN(string[] alpn_list)
	{
		() @trusted { m_clientOffers.clear(); } ();
		foreach (alpn; alpn_list)
			() @trusted { m_clientOffers ~= alpn.idup; } ();
	}

	/** Creates a new stream associated to this context.
	*/
	TLSStream createStream(InterfaceProxy!Stream underlying, TLSStreamState state, string peer_name = null, NetworkAddress peer_address = NetworkAddress.init)
	{
		if (!m_certChecked)
			() @trusted { checkCert(); } ();
		return new BotanTLSStream(underlying, this, state, peer_name, peer_address);
	}

	/** Specifies the validation level of remote peers.

		The default mode for TLSContextKind.client is
		TLSPeerValidationMode.trustedCert and the default for
		TLSContextKind.server is TLSPeerValidationMode.none.
	*/
	@property void peerValidationMode(TLSPeerValidationMode mode) {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			credentials.m_validationMode = mode;
			return;
		}
		else assert(false, "Cannot handle peerValidationMode if CustomTLSCredentials is not used");
	}
	/// ditto
	@property TLSPeerValidationMode peerValidationMode() const {
		if (auto credentials = cast(const(CustomTLSCredentials))m_credentials) {
			return credentials.m_validationMode;
		}
		else assert(false, "Cannot handle peerValidationMode if CustomTLSCredentials is not used");
	}

	/** An optional user callback for peer validation.

		Peer validation callback is unused in Botan. Specify a custom TLS Policy to handle peer certificate data.
	*/
	@property void peerValidationCallback(TLSPeerValidationCallback callback) { assert(false, "Peer validation callback is unused in Botan. Specify a custom TLS Policy to handle peer certificate data."); }
	/// ditto
	@property inout(TLSPeerValidationCallback) peerValidationCallback() inout { return TLSPeerValidationCallback.init; }

	/** The maximum length of an accepted certificate chain.

		Any certificate chain longer than this will result in the TLS
		negitiation failing.

		The default value is 9.
	*/
	@property void maxCertChainLength(int val) {

		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			credentials.m_max_cert_chain_length = val;
			return;
		}
		else assert(false, "Cannot handle maxCertChainLength if CustomTLSCredentials is not used");
	}
	/// ditto
	@property int maxCertChainLength() const {
		if (auto credentials = cast(const(CustomTLSCredentials))m_credentials) {
			return credentials.m_max_cert_chain_length;
		}
		else assert(false, "Cannot handle maxCertChainLength if CustomTLSCredentials is not used");
	}

	void setCipherList(string list = null) { assert(false, "Incompatible interface method requested"); }

	/** Set params to use for DH cipher.
	 *
	 * By default the 2048-bit prime from RFC 3526 is used.
	 *
	 * Params:
	 * pem_file = Path to a PEM file containing the DH parameters. Calling
	 *    this function without argument will restore the default.
	 */
	void setDHParams(string pem_file=null) { assert(false, "Incompatible interface method requested"); }

	/** Set the elliptic curve to use for ECDH cipher.
	 *
	 * By default a curve is either chosen automatically or  prime256v1 is used.
	 *
	 * Params:
	 * curve = The short name of the elliptic curve to use. Calling this
	 *    function without argument will restore the default.
	 *
	 */
	void setECDHCurve(string curve=null) { assert(false, "Incompatible interface method requested"); }

	/// Sets a certificate file to use for authenticating to the remote peer
	void useCertificateChainFile(string path) {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			m_certChecked = false;
			() @trusted { credentials.m_server_cert = X509Certificate(path); } ();
			return;
		}
		else assert(false, "Cannot handle useCertificateChainFile if CustomTLSCredentials is not used");
	}

	/// Sets the private key to use for authenticating to the remote peer based
	/// on the configured certificate chain file.
	/// todo: Use passphrase?
	void usePrivateKeyFile(string path) {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			import botan.pubkey.pkcs8 : loadKey;
			credentials.m_key = () @trusted { return loadKey(path, m_rng); } ();
			return;
		}
		else assert(false, "Cannot handle usePrivateKeyFile if CustomTLSCredentials is not used");
	}

	/** Sets the list of trusted certificates for verifying peer certificates.

		If this is a server context, this also entails that the given
		certificates are advertised to connecting clients during handshake.

		On Linux, the system's root certificate authority list is usually
		found at "/etc/ssl/certs/ca-certificates.crt",
		"/etc/pki/tls/certs/ca-bundle.crt", or "/etc/ssl/ca-bundle.pem".
	*/
	void useTrustedCertificateFile(string path) {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			auto store = () @trusted { return new CertificateStoreInMemory; } ();
			() @trusted { store.addFromFile(path); } ();
			() @trusted { credentials.m_stores.pushBack(store); } ();
			return;
		}
		else assert(false, "Cannot handle useTrustedCertificateFile if CustomTLSCredentials is not used");
	}

	void useSystemCertificateStore() {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			credentials.useSystemCertificateStore();
			return;
		}
		assert(false, "Cannot handle useSystemCertificateStore if CustomTLSCredentials is not used");
	}

	@property void ocspChecking(bool enabled) {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			credentials.m_ocsp_checking = enabled;
			return;
		}
		assert(false, "Cannot handle ocspChecking if CustomTLSCredentials is not used");
	}
	@property bool ocspChecking() const {
		if (auto credentials = cast(const(CustomTLSCredentials))m_credentials) {
			return credentials.m_ocsp_checking;
		}
		assert(false, "Cannot handle ocspChecking if CustomTLSCredentials is not used");
	}

	void addTrustedCertificate(ubyte[] cert_data) {
		if (auto credentials = cast(CustomTLSCredentials)m_credentials) {
			credentials.addTrustedCertificate(cert_data);
			return;
		}
		assert(false, "Cannot handle addTrustedCertificate if CustomTLSCredentials is not used");
	}

	private SNIContextSwitchInfo sniHandler(string hostname)
	{
		auto ctx = onSNI(hostname);
		if (!ctx) return SNIContextSwitchInfo.init;
		SNIContextSwitchInfo chgctx;
		chgctx.session_manager = ctx.m_sessionManager;
		chgctx.credentials = ctx.m_credentials;
		chgctx.policy = ctx.m_policy;
		chgctx.next_proto = &ctx.nextProtocolHandler;
		//chgctx.user_data = cast(void*)hostname.toStringz();
		return chgctx;
	}

	private string nextProtocolHandler(in Vector!string offers) {
		enforce(m_kind == TLSContextKind.server, "Attempted ALPN selection on a " ~ m_kind.to!string);
		if (m_serverCb !is null)
			return m_serverCb(offers[]);
		else return "";
	}

	private BotanTLSContext onSNI(string hostname) {
		if (m_kind != TLSContextKind.serverSNI)
			return null;

		TLSContext ctx = m_sniCallback(hostname);
		if (auto bctx = cast(BotanTLSContext) ctx) {
			// Since this happens in a BotanTLSStream, the stream info (r/w callback) remains the same
			return bctx;
		}

		// We cannot use anything else than a Botan stream, and any null value with serverSNI is a failure
		throw new Exception("Could not find specified hostname");
	}

	private void checkCert() {
		m_certChecked = true;
		if (m_kind == TLSContextKind.client) return;
		if (auto creds = cast(CustomTLSCredentials) m_credentials) {
			auto sigs = m_policy.allowedSignatureMethods();
			import botan.asn1.oids : OIDS;
			import vibe.core.log : logDebug;
			auto sig_algo = OIDS.lookup(creds.m_server_cert.signatureAlgorithm().oid());
			import std.range : front;
			import std.algorithm.iteration : splitter;
			string sig_algo_str = sig_algo.splitter("/").front.to!string;
			logDebug("Certificate algorithm: %s", sig_algo_str);
			bool found;
			foreach (sig; sigs[]) {
				if (sig == sig_algo_str) {
					found = true; break;
				}
			}
			assert(found, "Server Certificate uses a signing algorithm that is not accepted in the server policy.");
		}
	}
}

/**
* TLS Policy as a settings object
*/
private class CustomTLSPolicy : TLSPolicy
{
	private {
		TLSProtocolVersion m_min_ver = TLSProtocolVersion.TLS_V10;
		TLSProtocolVersion m_max_ver;
		TLSProtocolVersion m_offer_ver;
		int m_min_dh_group_size = 2048;
		Vector!TLSCiphersuite m_pri_ciphersuites;
		Vector!string m_pri_ecc_curves;
		Duration m_session_lifetime = 24.hours;
		bool m_pri_ciphers_exclusive;
		bool m_pri_curves_exclusive;
	}

	/// Sets the minimum acceptable protocol version
	@property void minProtocolVersion(TLSProtocolVersion ver) { m_min_ver = ver; }

	/// Get the minimum acceptable protocol version
	@property TLSProtocolVersion minProtocolVersion() { return m_min_ver; }

	@property void maxProtocolVersion(TLSProtocolVersion ver) { m_max_ver = ver; }
	@property TLSProtocolVersion maxProtocolVersion() { return m_max_ver; }

	@property void offerProtocolVersion(TLSProtocolVersion ver) { m_offer_ver = ver; }
	@property TLSProtocolVersion offerProtocolVersion() { return m_offer_ver; }

	/// Same selectable range as vibe-stream OpenSSL: min 1.2, max 1.3
	/// when TLS 1.3 is compiled. botan `latestTlsVersion()` stays 1.2.
	static TLSProtocolVersion osslStyleLatest()
	{
		static if (BOTAN_HAS_TLS_13)
			return TLSProtocolVersion(TLSProtocolVersion.TLS_V13);
		return TLSProtocolVersion.latestTlsVersion();
	}

	/// Map a vibe `TLSVersion` onto min / offer / max. `any` and
	/// `tls1_2` match OpenSSL (min 1.2, max/offer 1.3 when compiled).
	void applyTlsVersion(TLSVersion ver)
	{
		m_max_ver = TLSProtocolVersion.init;
		final switch (ver) {
			case TLSVersion.any:
				m_min_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V12);
				m_offer_ver = osslStyleLatest();
				m_max_ver = osslStyleLatest();
				break;
			case TLSVersion.ssl3:
			case TLSVersion.tls1:
				m_min_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V10);
				m_offer_ver = osslStyleLatest();
				m_max_ver = osslStyleLatest();
				break;
			case TLSVersion.tls1_1:
				m_min_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V11);
				m_offer_ver = osslStyleLatest();
				m_max_ver = osslStyleLatest();
				break;
			case TLSVersion.tls1_2:
				m_min_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V12);
				m_offer_ver = osslStyleLatest();
				m_max_ver = osslStyleLatest();
				break;
			case TLSVersion.tls1_3:
				m_min_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V13);
				m_offer_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V13);
				m_max_ver = TLSProtocolVersion(TLSProtocolVersion.TLS_V13);
				break;
			case TLSVersion.dtls1:
				m_min_ver = TLSProtocolVersion(TLSProtocolVersion.DTLS_V12);
				m_offer_ver = TLSProtocolVersion.latestDtlsVersion();
				break;
		}
	}

	@property void minDHGroupSize(int sz) { m_min_dh_group_size = sz; }
	@property int minDHGroupSize() { return m_min_dh_group_size; }

	/// Add a cipher suite to the priority ciphers with lowest ordering value
	void addPriorityCiphersuites(TLSCiphersuite[] suites) { m_pri_ciphersuites ~= suites; }

	@property TLSCiphersuite[] ciphers() { return m_pri_ciphersuites[]; }

	/// Set to true to use excuslively priority ciphers passed through "addCiphersuites"
	@property void priorityCiphersOnly(bool b) { m_pri_ciphers_exclusive = b; }
	@property bool priorityCiphersOnly() { return m_pri_ciphers_exclusive; }

	void addPriorityCurves(string[] curves) {
		m_pri_ecc_curves ~= curves;
	}
	@property string[] priorityCurves() { return m_pri_ecc_curves[]; }

	/// Uses only priority curves passed through "add"
	@property void priorityCurvesOnly(bool b) { m_pri_curves_exclusive = b; }
	@property bool priorityCurvesOnly() { return m_pri_curves_exclusive; }

	override string chooseCurve(in Vector!string curve_names) const
	{
		import std.algorithm : countUntil;
		foreach (curve; m_pri_ecc_curves[]) {
			if (curve_names[].countUntil(curve) != -1)
				return curve;
		}

		if (!m_pri_curves_exclusive)
			return super.chooseCurve((cast(Vector!string)curve_names).move);
		return "";
	}

	override Vector!string allowedEccCurves() const {
		Vector!string ret;
		if (!m_pri_ecc_curves.empty)
			ret ~= m_pri_ecc_curves[];
		if (!m_pri_curves_exclusive)
			ret ~= super.allowedEccCurves();
		return ret;
	}

	override Vector!ushort ciphersuiteList(TLSProtocolVersion _version, bool have_srp) const {
		Vector!ushort ret;
		if (m_pri_ciphersuites.length > 0) {
			foreach (suite; m_pri_ciphersuites) {
				ret ~= suite.ciphersuiteCode();
			}
		}

		if (!m_pri_ciphers_exclusive) {
			ret ~= super.ciphersuiteList(_version, have_srp);
		}

		return ret;
	}

	override bool acceptableProtocolVersion(TLSProtocolVersion _version) const
	{
		if (m_min_ver != TLSProtocolVersion.init) {
			if (_version.isDatagramProtocol() != m_min_ver.isDatagramProtocol())
				return false;
			if (_version < m_min_ver)
				return false;
		}
		if (m_max_ver != TLSProtocolVersion.init) {
			if (_version.isDatagramProtocol() != m_max_ver.isDatagramProtocol())
				return false;
			if (_version > m_max_ver)
				return false;
		}
		if (m_min_ver == TLSProtocolVersion.init && m_max_ver == TLSProtocolVersion.init)
			return super.acceptableProtocolVersion(_version);
		return true;
	}

	override TLSProtocolVersion latestSupportedVersion(bool datagram) const
	{
		if (m_offer_ver.valid)
			return m_offer_ver;
		return super.latestSupportedVersion(datagram);
	}

	override bool allowServerInitiatedRenegotiation() const {
		return false;
	}

	/// TLS 1.3 CertificateVerify: ECDSA / Ed25519 before RSA-PSS.
	/// Ephemeral ECDH group preference is `allowedEccCurves` (x25519 first).
	override Vector!string allowedSignatureMethods() const {
		Vector!string sigs = Vector!string([
			"ECDSA",
			"ECDHE_ECDSA",
			"Ed25519",
			"RSA",
			"ECDHE_RSA",
		]);
		static if (is(typeof(BOTAN_HAS_ED448)) && BOTAN_HAS_ED448)
			sigs.pushBack("Ed448");
		return sigs.move;
	}

	override Duration sessionTicketLifetime() const {
		return m_session_lifetime;
	}

	override size_t minimumDhGroupSize() const {
		return m_min_dh_group_size;
	}
}


private class CustomTLSCredentials : TLSCredentialsManager
{
	private {
		TLSPeerValidationMode m_validationMode = TLSPeerValidationMode.none;
		int m_max_cert_chain_length = 9;
		SymmetricKey m_session_ticket_key;
	}

	public {
		X509Certificate m_server_cert, m_ca_cert;
		PrivateKey m_key;
		Vector!CertificateStore m_stores;
		bool m_ocsp_checking;
	}
	private bool m_system_store_loaded;

	this() { initSessionTicketKey(); }

	// Client constructor
	this(TLSPeerValidationMode validation_mode = TLSPeerValidationMode.checkPeer) {
		m_validationMode = validation_mode;
		initSessionTicketKey();
	}

	// Server constructor
	this(X509Certificate server_cert, X509Certificate ca_cert, PrivateKey server_key)
	{
		m_server_cert = server_cert;
		m_ca_cert = ca_cert;
		m_key = server_key;
		initSessionTicketKey();
		auto store = new CertificateStoreInMemory;

		store.addCertificate(m_ca_cert);
		m_stores.pushBack(store);
		m_validationMode = TLSPeerValidationMode.none;
	}

	void addTrustedCertificate(ubyte[] cert)
	{
		import botan.utils.types : Vector;
		Vector!ubyte cert_vec = Vector!ubyte(cert);
		if (m_stores.length == 0) {
			auto store = new CertificateStoreInMemory;
			store.addCertificate(X509Certificate(cert_vec));
			m_stores.pushBack(store);
		} else
			(cast(CertificateStoreInMemory)m_stores[0]).addCertificate(X509Certificate(cert_vec));
	}

	void useSystemCertificateStore()
	{
		if (m_system_store_loaded)
			return;
		m_system_store_loaded = true;
		static if (BOTAN_HAS_CERTSTORE_SYSTEM) {
			import botan.cert.x509.certstor_system;
			try {
				m_stores.pushBack(new CertificateStoreSystem);
				return;
			} catch (Exception e) {
				import vibe.core.log : logWarn;
				logWarn("System certificate store unavailable: %s", e.msg);
			}
		}
		loadPosixCaBundles();
	}

	private void loadPosixCaBundles()
	{
		import std.file : exists, isFile;
		static immutable paths = [
			"/etc/ssl/certs/ca-certificates.crt",
			"/etc/pki/tls/certs/ca-bundle.crt",
			"/etc/ssl/ca-bundle.pem",
			"/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem",
			"/etc/ssl/cert.pem",
			"/usr/local/etc/openssl/cert.pem",
			"/opt/homebrew/etc/openssl@3/cert.pem",
		];
		foreach (path; paths) {
			if (!exists(path) || !isFile(path))
				continue;
			try {
				auto store = new CertificateStoreInMemory;
				store.addFromFile(path);
				m_stores.pushBack(store);
				return;
			} catch (Exception e) {
				import vibe.core.log : logWarn;
				logWarn("Failed to load CA bundle %s: %s", path, e.msg);
			}
		}
	}

	override Vector!CertificateStore trustedCertificateAuthorities(in string, in string)
	{
		if (m_stores.length == 0 && (m_validationMode & TLSPeerValidationMode.checkTrust))
			useSystemCertificateStore();
		if (m_stores.length == 0)
			return Vector!CertificateStore.init;
		return m_stores.clone;
	}

	override Vector!X509Certificate certChain(const ref Vector!string cert_key_types, in string type, in string)
	{
		Vector!X509Certificate chain;

		if (type == "tls-server")
		{
			bool have_match = false;
			foreach (cert_key_type; cert_key_types[]) {
				if (cert_key_type == m_key.algoName) {
					enforce(m_server_cert, "Private Key was defined but no corresponding server certificate was found.");
					have_match = true;
				}
			}

			if (have_match)
			{
				chain.pushBack(m_server_cert);
				if (m_ca_cert) chain.pushBack(m_ca_cert);
			}
		}

		return chain.move();
	}

	override void verifyCertificateChain(in string type, in string purported_hostname, const ref Vector!X509Certificate cert_chain)
	{
		if (cert_chain.empty)
			throw new InvalidArgument("Certificate chain was empty");

		if (m_validationMode == TLSPeerValidationMode.validCert)
		{
			auto trusted_CAs = trustedCertificateAuthorities(type, purported_hostname);

			PathValidationRestrictions restrictions;
			restrictions.maxCertChainLength = m_max_cert_chain_length;
			restrictions.ocspAllIntermediates = m_ocsp_checking;

			auto result = x509PathValidate(cert_chain, restrictions, trusted_CAs);

			if (!result.successfulValidation())
				throw new Exception("Certificate validation failure: " ~ result.resultString());

			if (!certInSomeStore(trusted_CAs, result.trustRoot()))
				throw new Exception("Certificate chain roots in unknown/untrusted CA");

			if (purported_hostname != "" && !cert_chain[0].matchesDnsName(purported_hostname))
				throw new Exception("Certificate did not match hostname");

			return;
		}

		if (m_validationMode & TLSPeerValidationMode.checkTrust) {
			auto trusted_CAs = trustedCertificateAuthorities(type, purported_hostname);

			PathValidationRestrictions restrictions;
			restrictions.maxCertChainLength = m_max_cert_chain_length;

			PathValidationResult result;
			try result = x509PathValidate(cert_chain, restrictions, trusted_CAs);
			catch (Exception e) { }

			if (!certInSomeStore(trusted_CAs, result.trustRoot()))
				throw new Exception("Certificate chain roots in unknown/untrusted CA");
		}

		// Commit to basic tests for other validation modes
		if (m_validationMode & TLSPeerValidationMode.checkCert) {
			import botan.asn1.asn1_time : X509Time;
			X509Time current_time = X509Time(Clock.currTime());
			// Check all certs for valid time range
			if (current_time < X509Time(cert_chain[0].startTime()))
				throw new Exception("Certificate is not yet valid");

			if (current_time > X509Time(cert_chain[0].endTime()))
				throw new Exception("Certificate has expired");

			if (cert_chain[0].isSelfSigned())
				throw new Exception("Certificate was self signed");
		}

		if (m_validationMode & TLSPeerValidationMode.checkPeer)
			if (purported_hostname != "" && !cert_chain[0].matchesDnsName(purported_hostname))
				throw new Exception("Certificate did not match hostname");


	}

	override PrivateKey privateKeyFor(in X509Certificate, in string, in string)
	{
		return m_key;
	}

	// Interface fallthrough
	override Vector!X509Certificate certChainSingleType(in string cert_key_type,
		in string type,
		in string context)
	{
		return super.certChainSingleType(cert_key_type, type, context);
	}

	override bool attemptSrp(in string type, in string context)
	{
		return super.attemptSrp(type, context);
	}

	override string srpIdentifier(in string type, in string context)
	{
		return super.srpIdentifier(type, context);
	}

	override string srpPassword(in string type, in string context, in string identifier)
	{
		return super.srpPassword(type, context, identifier);
	}

	override bool srpVerifier(in string type,
		in string context,
		in string identifier,
		ref string group_name,
		ref BigInt verifier,
		ref Vector!ubyte salt,
		bool generate_fake_on_unknown)
	{
		return super.srpVerifier(type, context, identifier, group_name, verifier, salt, generate_fake_on_unknown);
	}

	override string pskIdentityHint(in string type, in string context)
	{
		return super.pskIdentityHint(type, context);
	}

	override string pskIdentity(in string type, in string context, in string identity_hint)
	{
		return super.pskIdentity(type, context, identity_hint);
	}

	override SymmetricKey psk(in string type, in string context, in string identity)
	{
		// Botan TLS servers issue RFC 5077 tickets only when this
		// PSK is present (see botan/tls/server.d have_session_ticket_key).
		// Same optimisation OpenSSL enables by default (session tickets
		// + SSL_SESS_CACHE_SERVER).
		if (type == "tls-server" && context == "session-ticket")
			return m_session_ticket_key;
		return super.psk(type, context, identity);
	}

	override bool hasPsk()
	{
		return true;
	}

	private void initSessionTicketKey()
	{
		auto rng = new AutoSeededRNG;
		m_session_ticket_key = SymmetricKey(rng, 32);
	}
}

private CustomTLSCredentials createCreds()
{

	import botan.rng.auto_rng;
	import botan.cert.x509.pkcs10;
	import botan.cert.x509.x509self;
	import botan.cert.x509.x509_ca;
	import botan.pubkey.algo.rsa;
	import botan.codec.hex;
	import botan.utils.types;
	scope rng = new AutoSeededRNG();
	auto ca_key = RSAPrivateKey(rng, 1024);
	scope(exit) ca_key.destroy();

	X509CertOptions ca_opts;
	ca_opts.common_name = "Test CA";
	ca_opts.country = "US";
	ca_opts.CAKey(1);

	X509Certificate ca_cert = x509self.createSelfSignedCert(ca_opts, *ca_key, "SHA-256", rng);

	auto server_key = RSAPrivateKey(rng, 1024);

	X509CertOptions server_opts;
	server_opts.common_name = "localhost";
	server_opts.country = "US";

	PKCS10Request req = x509self.createCertReq(server_opts, *server_key, "SHA-256", rng);

	X509CA ca = X509CA(ca_cert, *ca_key, "SHA-256");

	auto now = Clock.currTime(UTC());
	X509Time start_time = X509Time(now);
	X509Time end_time = X509Time(now + 365.days);

	X509Certificate server_cert = ca.signRequest(req, rng, start_time, end_time);

	return new CustomTLSCredentials(server_cert, ca_cert, server_key.release());

}

private {
	__gshared CustomTLSPolicy gs_default_policy;
}

unittest {
	auto p12 = new CustomTLSPolicy();
	p12.applyTlsVersion(TLSVersion.tls1_2);
	assert(p12.minProtocolVersion() == TLSProtocolVersion(TLSProtocolVersion.TLS_V12));
	assert(p12.offerProtocolVersion() == CustomTLSPolicy.osslStyleLatest());
	assert(p12.acceptableProtocolVersion(TLSProtocolVersion(TLSProtocolVersion.TLS_V12)));
	assert(!p12.acceptableProtocolVersion(TLSProtocolVersion(TLSProtocolVersion.TLS_V10)));
	static if (BOTAN_HAS_TLS_13)
		assert(p12.acceptableProtocolVersion(TLSProtocolVersion(TLSProtocolVersion.TLS_V13)));
	else
		assert(!p12.acceptableProtocolVersion(TLSProtocolVersion(TLSProtocolVersion.TLS_V13)));

	auto p13 = new CustomTLSPolicy();
	p13.applyTlsVersion(TLSVersion.tls1_3);
	assert(p13.minProtocolVersion() == TLSProtocolVersion(TLSProtocolVersion.TLS_V13));
	assert(p13.offerProtocolVersion() == TLSProtocolVersion(TLSProtocolVersion.TLS_V13));
	assert(p13.acceptableProtocolVersion(TLSProtocolVersion(TLSProtocolVersion.TLS_V13)));
	assert(!p13.acceptableProtocolVersion(TLSProtocolVersion(TLSProtocolVersion.TLS_V12)));
	assert(p13.latestSupportedVersion(false) == TLSProtocolVersion(TLSProtocolVersion.TLS_V13));

	auto anyp = new CustomTLSPolicy();
	anyp.applyTlsVersion(TLSVersion.any);
	assert(anyp.offerProtocolVersion() == CustomTLSPolicy.osslStyleLatest());
	assert(TLSProtocolVersion.latestTlsVersion() == TLSProtocolVersion(TLSProtocolVersion.TLS_V12));

	auto ctx12 = new BotanTLSContext(TLSContextKind.client, TLSVersion.tls1_2);
	assert(ctx12.defaultProtocolOffer == CustomTLSPolicy.osslStyleLatest());
	assert(ctx12.peerValidationMode == TLSPeerValidationMode.trustedCert);
	assert(!ctx12.ocspChecking);
	ctx12.ocspChecking = true;
	assert(ctx12.ocspChecking);

	auto ctx13 = new BotanTLSContext(TLSContextKind.server, TLSVersion.tls1_3);
	assert(ctx13.defaultProtocolOffer == TLSProtocolVersion(TLSProtocolVersion.TLS_V13));
	assert(ctx13.peerValidationMode == TLSPeerValidationMode.none);
}
