# SAML 2.0 XML Signature Wrapping, OAuth 2.1 / OIDC PKCE & Mix-Up Downgrades, and JWT / ECDSA Verification Confusion

## Summary

Federated authentication and single sign-on (`SSO`) protocols—**SAML 2.0**, **OAuth 2.0 / 2.1**, **OpenID Connect (`OIDC`)**, and **JOSE (`JWT`/`JWS`)**—repeatedly suffer complete authentication bypasses even when underlying cryptographic hash and cipher primitives (`SHA-256`, `RSA-PSS`, `HMAC`, `P-256`) are unbroken. Across primary-source inspections of `russellhaering/goxmldsig` (`10e2e6555035897cd38d90631553af153d2ffde6`), `mattermost/xml-roundtrip-validator` (`3079e7b80fcab1eae8b64108e9157061b0cb4f35`), `lsh123/xmlsec` (`7469c2258e100afe7b42fcb8241d527fbf5898df`), `golang-jwt/jwt` (`f411663679b83c5b1005f8c54da427281de64680`), `panva/jose` (`d1e200f22d2bc66cd2ed6cc48fc622b6f1765cc5`), `openid/AppAuth-JS` (`cbabdaf2747563cfac178e1aa89aa34c1c191d18`), and `openjdk/jdk` (`510deb132b0c5ff6fefdf7bde56d82223e927b69`), alongside Somorovsky et al. (`USENIX Security 2012`), Fett, Küsters & Schmitz (`DOI 10.1145/2976749.2978385`, `IEEE CSF 2017`), `IETF RFC 9700`, and `IETF RFC 8725`, four structural vulnerability classes account for the vast majority of real-world SSO compromises:

1. **SAML 2.0 XML Signature Wrapping (`XSW`), Comment-Truncation (`CVE-2017-11427`..`11433`), and XML Round-Trip Differentials (`CVE-2020-29509`..`29511`) (`Basis: normative + source + execution`)**: XML Digital Signatures (`XMLDSig`) sign a canonicalized subset of DOM nodes selected by `Reference URI="#id"` or XPath transforms, while Service Providers (`SP`s) extract subject claims via separate DOM/XPath queries (`.//Assertion/NameID`). Decoupling the verified subtree from the consumed document enables `8` classic `XSW` variants (`Somorovsky et al. 2012`). Even within a single signed `<NameID>admin@corp.example<!--x-->.attacker.net</NameID>` element, Exclusive XML Canonicalization without comments (`http://www.w3.org/2001/10/xml-exc-c14n#`) strips `<!--x-->` and verifies the attacker's valid `admin@corp.example.attacker.net` signature, whereas DOM `firstChild.nodeValue` / Python `ElementTree` `.text` truncates at the comment node and logs the attacker in as **`admin@corp.example`** (`Duo Labs CVE-2017-11427`). Furthermore, Go `encoding/xml` namespace-prefix round-trip mutations (`CVE-2020-29509`) allow element-tag spoofing unless raw input bytes first pass token-stream round-trip validation (`mattermost/xml-roundtrip-validator/validator.go:39`) and `Validate` returns **exclusively a freshly re-parsed document over the verified canonical bytes** (`goxmldsig/validate.go:363-370`).
2. **OAuth 2.1 / OIDC `PKCE` Downgrades, `redirect_uri` Parser Differentials, and `IdP` Mix-Up Attacks (`Basis: normative + source + execution`)**: In `openid/AppAuth-JS` (`src/authorization_request.ts:95-106`), `setupCodeVerifier()` catches `crypto.deriveChallenge` rejections, logs `'Unable to generate PKCE challenge. Not using PKCE'`, and **silently omits `code_challenge` and `code_challenge_method` (`fail-open`)** even when `usePkce = true`! On the server side, accepting `code_challenge_method=plain` or omitting `code_challenge` checks when `code_verifier` is absent enables authorization-code interception, while prefix-based `redirect_uri` matching (`startswith("https://app.corp.example")`) leaks codes to `https://app.corp.example.attacker.net`. Under the Fett–Küsters–Schmitz (`FKS`) Web Infrastructure Model (`CCS 2016`, `arXiv:1601.01229`), multi-IdP Relying Parties remain vulnerable to **IdP Mix-Up** unless authorization responses bind the exact issuer (`iss`, `RFC 9207` / `RFC 9700`) and distinct per-IdP redirect endpoints or `state`-bound issuer records.
3. **JWT / JWS Algorithm Confusion (`RS256 -> HS256`), `alg: "none"`, and Unauthenticated Key-URL (`jku`/`x5u`) SSRF (`Basis: normative + source + execution`)**: Trusting an unverified JOSE header's `"alg"` field before key resolution allows attackers to set `"alg": "none"` (`blocked in golang-jwt/none.go:27 only via magic type unsafeNoneMagicConstant; structurally absent in panva/jose`) or rewrite `"alg": "RS256"` to `"HS256"`, computing an HMAC-SHA256 tag using the server's publicly distributed RSA SPKI bytes! Contrasting `golang-jwt/jwt` (`parser.go:53-98`, where `validMethods` defaults to `nil` and `keyFunc` returns untyped `any`) against `panva/jose` (`src/lib/key.ts:43-90`, where `prepareKey` rejects public keys for `secret == true` algorithms regardless of options) proves that **binding cryptographic key types directly to algorithm families eliminates `RS256 -> HS256` confusion by construction**.
4. **Degenerate Elliptic-Curve Group Boundary Bypasses (`CVE-2022-21449` "Psychic Signatures") (`Basis: source + execution + derived`)**: When OpenJDK 15 rewritten ECDSA verification in pure Java, omitting $r, s \in [1, n-1]$ range checks prior to Fermat's Little Theorem modular inversion ($s^{-1} \equiv s^{n-2} \pmod n$, where $0^{n-2} \equiv 0$) caused `(r = 0, s = 0)` to evaluate $u_1 = 0, u_2 = 0$, $R' = \mathcal{O} \mapsto x = 0 \equiv r$, returning **`true` for every message and every ECDSA public key** across JWT, SAML, OIDC, WebAuthn, and TLS (`fixed in openjdk/jdk ECDSAOperations.java:215-219`).

---

## Applicability

This report applies to identity providers (`IdP`s), Relying Parties (`RP`s) / Service Providers (`SP`s), API gateways, zero-trust service meshes, OAuth/OIDC mobile & browser SDKs, and formal protocol/parser verifiers across seven pinned repositories and three foundational standards/papers:

- **XML Digital Signature & SAML 2.0 Engines**: `russellhaering/goxmldsig` (`10e2e6555035897cd38d90631553af153d2ffde6`), `mattermost/xml-roundtrip-validator` (`3079e7b80fcab1eae8b64108e9157061b0cb4f35`), and Aleksey Sanin's C `XMLSec` library `lsh123/xmlsec` (`7469c2258e100afe7b42fcb8241d527fbf5898df`, underlying Python `xmlsec`, Ruby, and Shibboleth/C bindings via `libxml2`).
- **JOSE / JWT Verification Libraries**: `golang-jwt/jwt` v5 (`f411663679b83c5b1005f8c54da427281de64680`) and `panva/jose` (`d1e200f22d2bc66cd2ed6cc48fc622b6f1765cc5`, WebCrypto TypeScript/JavaScript reference implementation), governed by `IETF RFC 7515`, `RFC 7797`, and `RFC 8725` (`BCP 225`).
- **OAuth 2.0 / 2.1 & OpenID Connect Clients / Servers**: `openid/AppAuth-JS` (`cbabdaf2747563cfac178e1aa89aa34c1c191d18`), analyzed against Fett, Küsters & Schmitz (`ACM CCS 2016` `DOI: 10.1145/2976749.2978385` and `IEEE CSF 2017` `arXiv:1704.08539`) and `IETF RFC 9700` (`BCP 240`, *OAuth 2.0 Security Best Current Practice*).
- **Elliptic-Curve Signature Verifiers**: `openjdk/jdk` (`510deb132b0c5ff6fefdf7bde56d82223e927b69`, `sun.security.ec.ECDSAOperations` and `ECDSASignature`), specifically characterizing the Java 15–18 `CVE-2022-21449` regression and its patched modular-order guards.

---

## Findings

### 1. SAML 2.0 XML Signature Wrapping (`XSW`), Comment Truncation, and Round-Trip Differentials

`Basis: normative + source + execution`

#### 1.1 Structural Disconnect Between `XMLDSig` Reference Verification and SP Claim Extraction
In OASIS SAML 2.0 Web SSO, an HTTP-POST `samlp:Response` carries one or more `saml:Assertion` elements alongside an enveloped `ds:Signature` (`http://www.w3.org/2000/09/xmldsig#`). Verification in `lsh123/xmlsec` (`7469c2258e100afe7b42fcb8241d527fbf5898df`, `src/xmldsig.c:336-355` `xmlSecDSigCtxVerify`) and `russellhaering/goxmldsig` (`10e2e6555035897cd38d90631553af153d2ffde6`, `validate.go:268-371` `validateSignature`) executes a two-level digest chain:
1. Canonicalize `<ds:SignedInfo>` (`C14N` or `Exc-C14N`) and verify `<ds:SignatureValue>` against the trusted IdP X.509 certificate;
2. For each `<ds:Reference URI="#target_id">`, locate the element matching `ID="target_id"`, apply listed `<ds:Transforms>` (removing `<ds:Signature>` for enveloped signatures and running `C14N`), and compare its SHA-256 digest against `<ds:DigestValue>`.

As established by Somorovsky et al. (*"On Breaking SAML: Be Whoever You Want to Be,"* USENIX Security 2012, breaking `11` of `14` major SAML frameworks), **cryptographic success on `xmlSecDSigCtxVerify(dsigCtx, sigNode)` proves only that *some* element in the document with `ID="target_id"` matched the IdP's signature—NOT that the root `<Response>` or first `<Assertion>` read by the application is that signed element!**

| SAML XML Differential Attack | Attacker Tree / Token Manipulation | Why Cryptographic Verification Passes | Why Naive SP Claim Extraction Reads Forged Identity |
| :--- | :--- | :--- | :--- |
| **`XSW-1..8` Wrapping** (`Somorovsky et al. 2012`) | Move legitimate signed `<Assertion ID="s1">` into `<samlp:Extensions>` (which uses schema `<any processContents="lax"/>` so XSD validation passes!) and place unsigned `<Assertion ID="evil"><NameID>root</NameID>` first | Verifier resolves `URI="#s1"` via `getElementById("s1")` or `//*[@ID='s1']`, hashing only the tucked-away legitimate node | SP calls `doc.find(".//Assertion/NameID")` (`tree-order first match`), reading `root` from the unsigned wrapper (`reproduced in verify_saml_oauth_jwt.py`) |
| **Duplicate-ID Shadowing** (`libxml2` / `etree` mismatch) | Inject `<Assertion ID="s1">` (unsigned) *and* `<Assertion ID="s1">` (signed) when XSD DTD `ID` uniqueness is disabled (to block `XXE`!) | Verifier picks last/DTD-indexed `@ID='s1'`, or `validateShape` is skipped (`goxmldsig/validate.go:380-396` explicitly guards child counts because Go `encoding/xml` *"last element will win"*!) | SP XPath `//*[@ID='s1'][1]` selects the first element with `ID="s1"` |
| **Comment Truncation (`CVE-2017-11427`..`11433`, Duo Labs)** | Authenticate legitimately at IdP as `admin@corp.example.attacker.net`, then insert `<!--c-->` mid-text: `<NameID>admin@corp.example<!--c-->.attacker.net</NameID>` | Default Exclusive C14N (`http://www.w3.org/2001/10/xml-exc-c14n#`, **not** `#WithComments`) strips all comment nodes, hashing exact string `admin@corp.example.attacker.net`! | DOM `el.firstChild.nodeValue` or Python `xml.etree.ElementTree` `el.text` (when comments are retained in DOM) returns only text **before** `<!--c-->` (`"admin@corp.example"`), leaving `".attacker.net"` unread in `comment.tail`! |
| **Go `encoding/xml` Prefix/Directive Round-Trip (`CVE-2020-29509`..`29511`)** | Craft malformed double-colon `<a:b:Assertion>` or nested `<<!-- -->Assertion>` directives | First unmarshal/re-marshal pass mutates namespace prefixes or drops tokens during Go `encoding/xml` serialization | Second consumer sees a structurally altered XML element hierarchy (`fixed via mattermost/xml-roundtrip-validator`) |

#### 1.2 Primary-Source Defenses in `goxmldsig` and `xml-roundtrip-validator`
Inspecting `russellhaering/goxmldsig` (`validate.go:310-371`) and `mattermost/xml-roundtrip-validator` (`validator.go:38-65`) demonstrates the exact **parse-verify-reparse isolation pattern** required to make XML signatures sound:
1. **Token-Level Round-Trip Gate (`validator.go:39`)**: Before building any DOM tree, `Validate(xmlReader)` tees raw input bytes into Go's `encoding/xml.Decoder` and re-encodes every token, aborting with `XMLRoundtripError` if any namespace, attribute, or directive mutates across round-trip.
2. **Re-Unmarshal `SignedInfo` Exclusively From Verified Canonical Bytes (`validate.go:315-320`)**: After `cert.CheckSignature(algo, canonicalSignedInfoBytes, decodedSignature)` succeeds, `goxmldsig` discards the input `sig.SignedInfo` struct and runs `xml.Unmarshal(canonicalSignedInfoBytes, signedInfo)` so no uncanonicalized sibling/duplicate element inside `<SignedInfo>` can influence `<Reference>` selection!
3. **Return Freshly Re-Parsed `referencedBytes` Root (`validate.go:363-370`)**:
   ```go
   // now only the referencedBytes is verified,
   // unmarshal into new etree
   doc := etree.NewDocument()
   err = doc.ReadFromBytes(referencedBytes)
   if err != nil {
       return nil, err
   }
   return doc.Root(), nil
   ```
   Because `referencedBytes` is the exact Exclusive-C14N byte buffer whose SHA-256 matched `signedDigestValue` (with all comments already stripped by non-comment C14N and all unreferenced outer `<Response>`/`<Extensions>` wrapper elements absent!), re-parsing `referencedBytes` into a brand-new `etree.Document` simultaneously defeats **both** `XSW-1..8` wrapping **and** `CVE-2017-11427` comment truncation (`safe_user == "admin@corp.example.attacker.net"` in `probes/verify_saml_oauth_jwt.py`).

---

### 2. OAuth 2.1 / OIDC `PKCE` Downgrades, `redirect_uri` Differentials, and `FKS` IdP Mix-Up

`Basis: normative + source + execution`

#### 2.1 Silent Client-Side `PKCE` Fail-Open in `openid/AppAuth-JS` (`src/authorization_request.ts:90-108`)
Proof Key for Code Exchange (`PKCE`, `RFC 7636`, mandated for *all* clients in `RFC 9700` §2.1.1 and OAuth 2.1) binds an authorization request (`code_challenge = BASE64URL(SHA256(code_verifier))`, `code_challenge_method = "S256"`) to the subsequent token-endpoint redeem request (`code_verifier`).

Direct source inspection of `openid/AppAuth-JS` (`cbabdaf2747563cfac178e1aa89aa34c1c191d18`, `src/authorization_request.ts:90-108`) reveals a textbook **fail-open downgrade** inside `AuthorizationRequest.setupCodeVerifier()`:
```ts
const codeVerifier = this.crypto.generateRandom(128);
const challenge: Promise<string|undefined> =
    this.crypto.deriveChallenge(codeVerifier).catch(error => {
      log('Unable to generate PKCE challenge. Not using PKCE', error);
      return undefined;
    });
return challenge.then(result => {
  if (result) {
    this.internal = this.internal || {};
    this.internal['code_verifier'] = codeVerifier;
    this.extras = this.extras || {};
    this.extras['code_challenge'] = result;
    this.extras['code_challenge_method'] = 'S256';
  }
});
```
Even when the caller explicitly passes `usePkce: boolean = true` (`default true` at `line 80`), **any runtime failure inside `crypto.deriveChallenge`** (such as `window.crypto.subtle` throwing in a non-HTTPS WebView, custom `Crypto` adapter failure, or CSP restriction) is caught, logged to console, and converted into `undefined`—sending an **unprotected non-PKCE OAuth 2.0 Authorization Request** over the network! If the Authorization Server also treats `code_challenge` as optional (`permissive OAuth 2.0 backward-compatibility mode`), both sides silently downgrade to zero PKCE protection. Sound `RFC 9700` / OAuth 2.1 posture requires: (a) client-side hard rejection (`Promise.reject`) when `usePkce == true` cannot compute `S256`, and (b) server-side rejection of missing `code_challenge` or `code_challenge_method == "plain"` (`RFC 9700` §2.1.1).

#### 2.2 Formal Web-Model `IdP` Mix-Up (`Fett, Küsters & Schmitz`) and `redirect_uri` Differentials
In *"A Comprehensive Formal Security Analysis of OAuth 2.0"* (`ACM CCS 2016`, `DOI: 10.1145/2976749.2978385`, `arXiv:1601.01229`) and *"The Web SSO Standard OpenID Connect: In-Depth Formal Security Analysis and Security Guidelines"* (`IEEE CSF 2017`, `arXiv:1704.08539`), Fett, Küsters, and Schmitz modeled browsers, HTTP redirects, `postMessage`, cookies, honest/malicious Relying Parties (`RP`s), and honest/malicious Identity Providers (`HIdP` vs. `AIdP`) in an expressive Dolev–Yao **Web Infrastructure Model (`WIM`)**, uncovering two systemic flaws:

1. **The `IdP` Mix-Up Attack**: Suppose an `RP` supports login via both honest `HIdP` and attacker-controlled `AIdP`, sharing a single callback URI `https://rp.example/cb`. User initiates login selecting `AIdP` (so `RP`'s session stores `session.selected_idp = AIdP`), but a network/MITM or malicious `AIdP` redirects the user's browser to `HIdP`'s authorization endpoint! User approves at `HIdP`, which redirects `code_H` back to `https://rp.example/cb?code=code_H&state=s`. Because `state = s` matches the user's browser session—and classic OAuth 2.0 authorization responses carry **no issuer identifier**—`RP` believes `code_H` came from `session.selected_idp == AIdP` and **POSTs `code_H` (or client credentials) directly to `AIdP`'s token endpoint**, handing complete control of the user's `HIdP` account to `AIdP`!
   - *Formal Resolution (`FKS` + `RFC 9207` + `RFC 9700` §4.4)*: Bind every authorization session `(state -> expected_iss)` AND require either (i) the `iss` response parameter (`RFC 9207`) verified byte-equal to `expected_iss` (`OIDC` ID Token `iss` if hybrid), or (ii) distinct per-IdP `redirect_uri` paths (`https://rp.example/cb/hidp` vs. `/cb/aidp`).
2. **`redirect_uri` Parser & Prefix Differentials (`RFC 9700` §4.1.1)**:
   - Naive prefix checks (`redirect_uri.startswith("https://app.corp.example")`) accept `https://app.corp.example.attacker.net/cb` (`verified in verify_saml_oauth_jwt.py`).
   - WHATWG URL (`browsers`: converts `\` to `/` in hierarchical schemes, so `https://attacker.net\@app.corp.example/cb` parses host `attacker.net`!) vs. `RFC 3986` (`server`: treats `\` as userinfo character before `@`, parsing host `app.corp.example`!) splits validation from browser navigation! `RFC 9700` §4.1.1 mandates **exact string comparison** against pre-registered canonical URIs containing zero userinfo, zero backslashes, and zero relative `..` path segments.

---

### 3. JWT / JWS Algorithm Confusion, Header Key-Injection, and `CVE-2022-21449` ECDSA Bypass

`Basis: normative + source + execution + derived`

#### 3.1 `golang-jwt/jwt` vs. `panva/jose`: Why Key-Type-to-Algorithm Binding Beats Runtime Options
A Compact JWS (`RFC 7515`) consists of `BASE64URL(ProtectedHeader) . BASE64URL(Payload) . BASE64URL(Signature)`. Crucially, **`ProtectedHeader` (`{"alg": ..., "kid": ..., "jku": ..., "crit": ...}`) is attacker-controlled input until `Signature` verification succeeds**.

Comparing `golang-jwt/jwt` (`f411663679b83c5b1005f8c54da427281de64680`) and `panva/jose` (`d1e200f22d2bc66cd2ed6cc48fc622b6f1765cc5`) reveals a decisive architectural contrast across four JOSE attack vectors:

| JOSE Attack Vector | `golang-jwt/jwt` v5 (`parser.go`, `hmac.go`, `none.go`) | `panva/jose` (`jws_verify.ts`, `key.ts`) | Root Architectural Lesson (`RFC 8725`) |
| :--- | :--- | :--- | :--- |
| **`alg: "none"` Unauthenticated Token** | `SigningMethodNone` is **registered globally in `init()`** (`none.go:16-20`), blocked only because `Verify` checks `_, ok := key.(unsafeNoneMagicConstant)` (`none.go:29`). If a buggy `keyFunc` returns `jwt.UnsafeAllowNoneSignatureType` for debug/test paths, `"none"` passes! | `"none"` is **completely absent from `jwsAlgorithm(alg)`** (`jws_verify.ts:159`); `jwtVerify` / `flattenedVerify` can never verify `"none"` under any key or option (`UnsecuredJWT` is a separate class/API). | Never include `"none"` in the signed-token `SigningMethod` registry (`make illegal states unrepresentable`). |
| **`RS256 -> HS256` Public-Key Confusion** | `p.validMethods` defaults to **`nil`** (`parser.go:53`). `keyFunc` returns `any` (`interface{}`): if a caller omits `jwt.WithValidMethods([]string{"RS256"})` and returns raw key `[]byte` (e.g., PEM/DER bytes from config), `SigningMethodHMAC.Verify` (`hmac.go:51`, `key.([]byte)`) **succeeds**, accepting an attacker HMAC forged with the public RSA key! (Returning `*rsa.PublicKey` fails `key.([]byte)` dynamically.) | `prepareKey(entry, key, 'verify')` (`key.ts:43-90`) enforces **disjoint key representations**: `secret == true` (`HS*`) accepts **only** `Uint8Array`, `CryptoKey{type:'secret'}`, or `JWK{kty:'oct'}`, throwing `TypeError` on any `public` `CryptoKey` or `RSA`/`EC` `JWK` *even when `options.algorithms` is omitted*! Also enforces `JWK.alg === alg` and `JWK.use === 'sig'` (`key.ts:12-38`). | Couple symmetric vs. asymmetric algorithm dispatch to **disjoint static key types** (`SymmetricOctetKey` vs. `AsymmetricPublicKey`), AND require explicit `algorithms` allowlists (`RFC 8725` §3.1). |
| **`jku` / `x5u` / Embedded `jwk` Injection** | Not auto-fetched by `Parser`, but custom `keyFunc` implementations reading `token.Header["jku"]` or `token.Header["jwk"]` routinely introduce SSRF or self-signed JWK bypasses! | `createRemoteJWKSet(new URL(pinnedJwksUri))` pins the JWKS origin at verifier construction time, ignoring attacker header `jku`/`x5u` completely. | Key-source URLs must come from **static verifier configuration** (or an `iss`-keyed allowlist), never raw `joseHeader.jku` (`RFC 8725` §3.3). |
| **Header / `crit` / `b64:false` Splitting (`RFC 7797`)** | Compact-only parser; ignores unrecognized header fields without `crit` enforcement. | `verifySignature` (`jws_verify.ts:125-133`) enforces `isDisjoint(protectedHeader, header)`, validates `crit` against recognized extensions (`validateCrit`), and checks ASCII/Unicode well-formedness on `b64: false` payloads (`L84-103`). | Reject duplicate/overlapping protected+unprotected header keys and unknown `crit` extensions fail-closed. |

#### 3.2 Mathematical & Source Anatomy of `CVE-2022-21449` ("Psychic Signatures" in OpenJDK 15–18)
Standard prime-order ECDSA over curve $E(\mathbb{F}_p)$ with generator $G$ of prime order $n$ and public key $Q = [d]G$ verifies message digest $e = \operatorname{Hash}(m) \bmod n$ and signature pair $(r, s)$ via four steps (`FIPS 186-5`):
1. **Mandatory Range Gate**: Verify $r \in [1, n-1]$ and $s \in [1, n-1]$; otherwise **reject**.
2. Compute $w = s^{-1} \bmod n$, $u_1 = e \cdot w \bmod n$, and $u_2 = r \cdot w \bmod n$.
3. Compute curve point $R' = [u_1]G + [u_2]Q$. If $R' = \mathcal{O}$ (point at infinity), **reject**.
4. Accept iff $x(R') \bmod n = r$.

Why did omitting Step 1 in OpenJDK 15 (`when porting sun.security.ec from C++ to Java`) create a **universal zero-knowledge forgery (`r = 0, s = 0`)** rather than throwing an `ArithmeticException: division by zero` at $s^{-1}$?
Inspecting `openjdk/jdk` (`510deb132b0c5ff6fefdf7bde56d82223e927b69`, `src/java.base/share/classes/sun/security/ec/ECDSAOperations.java:215-235`) reveals the **constant-time finite-field arithmetic interaction**:
- Constant-time modular arithmetic (`IntegerModuloP.multiplicativeInverse()`, `line 229`) avoids variable-time Euclidean GCD branches by computing $s^{n-2} \bmod n$ via Fermat's Little Theorem! For $s = 0$, $0^{n-2} \bmod n = \mathbf{0}$ (total function, zero exception!).
- Multiplying by $w = 0$ yields $u_1 = e \cdot 0 = 0$ and $u_2 = 0 \cdot 0 = 0$.
- Constant-time scalar multiplication evaluates $[0]G + [0]Q = \mathcal{O}$ in homogeneous projective coordinates $(X : Y : Z) = (0 : 1 : 0)$, and projects back to affine $x = X \cdot Z^{p-2} \bmod p = 0 \cdot 0 = \mathbf{0}$!
- The final equality check tests $0 \stackrel{?}{=} r \pmod n$, which for $r = 0$ evaluates `0 == 0` $\implies$ **`true` for every message $m$ and every public key $Q$** (`verified on prime-order curve n = 31 in probes/verify_saml_oauth_jwt.py`)!
- Lines `215-219` of `ECDSAOperations.java` restore Step 1 explicitly prior to `orderField.getElement`:
  ```java
  BigInteger rb = new BigInteger(1, r);
  BigInteger sb = new BigInteger(1, s);
  if (rb.signum() == 0 || sb.signum() == 0
          || rb.compareTo(mod) >= 0 || sb.compareTo(mod) >= 0) {
      return false;
  }
  ```
  **General Verification Law**: Constant-time Fermat inversion ($x^{p-2} \bmod p$) silently extends $x^{-1}$ to a total ring operation mapping $0 \mapsto 0$! Any cryptographic verifier replacing partial Euclidean inversion with total Fermat exponentiation **must** pair it with explicit non-zero subgroup/scalar type refinements (`NonZeroScalar<n>`).

---

### 4. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Resource Axis | SAML 2.0 + `XMLDSig` (`goxmldsig` + `xml-roundtrip-validator` / `xmlsec`) | JOSE `JWT`/`JWS` (`golang-jwt` / `panva/jose`) | Canonical Binary Envelope (`PASETO` v4 / `COSE_Sign1` `RFC 9052`) |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring Velocity** | Secure RP integration LoC & configuration footgun surface | `~150–400 LoC` (`X509Store`, C14N method, `IdAttribute`, Audience/NotOnOrAfter, `rtvalidator`, verified-root re-binding; high historical CVE rate) | `~25–60 LoC` (`must` configure `algorithms`/`WithValidMethods`, `iss`, `aud`, `exp`, clock skew, JWKS pinning) | **`~8–15 LoC`** (`v4.public` pins Ed25519 + PAE framing; `0` attacker-selectable `"alg"` header!) |
| **`L2` Toolchain Build Time** | Library & native dependency build latency | `lsh123/xmlsec` + `libxml2` + `OpenSSL` C autotools/CMake build: `~45–120 s`; pure-Go `goxmldsig`: `~1.8 s` | Pure Go (`golang-jwt`) or zero-dep WebCrypto TS (`panva/jose`): **`< 1.0 s`** (`0` C FFI toolchain risk) | Pure Rust/Go/TS Ed25519 + BLAKE2b/CBOR build: **`< 1.0 s`** |
| **`L3` Compilation & Protocol Check** | Static typechecking / formal model (`Tamarin` / `ProVerif` / `FKS`) | Unbounded XPath + C14N tree rewrites are undecidable/intractable in symbolic provers; requires canonical byte-isolation discipline | Key-type-indexed API (`Verifier<Ed25519PublicKey>`) typechecks in **`< 5 ms`**; Tamarin/FKS OAuth+OIDC models verify in `~2–40 s` | Deterministic `PAE` / `Sig_structure` CBOR tuple bijection verifies in **`< 2 ms`** |
| **`L4` Runtime Execution Speed** | Per-token parse + canonicalize + crypto verify latency | **`~0.35–1.80 ms/assertion`**: `rtvalidator` double-tokenize + `etree` copy + `Exc-C14N` namespace walk + RSA-2048 (`~40–90 us`) | **`~25–95 us/token`**: `3`-slice `split('.')` + Base64url + `P-256` ECDSA (`~45 us`) or `HMAC-SHA256` (`~1.2 us`, `0` C14N!) | **`~30–55 us/token`**: single `Ed25519` verify (`~40 us` batchable) + length-prefixed `PAE` (`0` JSON header re-parse!) |
| **`L5` Audit / Replay Verification** | Independent gateway / proxy token admission speed | Heavy (`requires full DOM + C14N engine inside edge proxy`, `> 300 us` tail latency risk on deeply nested XML!) | Fast edge admission (`~30–80 us` in Wasm/Envoy/Cloudflare Workers WebCrypto) | **Ultra-fast constant-shape admission (`< 45 us`, `0` dynamic tree allocation)** |
| **`L6` RAM, Wire & Binary Footprints** | Token wire bytes, parser heap allocations & library size | SAML assertion wire size **`4–16 KiB`** (`Base64` XML); `3x` DOM copy amplification (`raw -> rtvalidator -> transformed -> reparsed root` = `~40–120 KiB`/req); `libxml2+xmlsec` `~2.2 MiB` `.so` | JWT wire size **`0.4–1.2 KiB`**; `< 4 KiB` per-request heap; `panva/jose` bundle `~18 KiB` minified | `COSE_Sign1` / `PASETO` wire size **`0.25–0.70 KiB`** (`binary CBOR`); **`0 B` heap** zero-copy slice verification |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived + source`

#### 5.1 `(C1)` Human Comprehensibility & Security Audit Ergonomics
1. **Why SAML `XSW` and Comment Truncation Defeat Human Code Review**:
   When a security engineer reads:
   ```python
   xmlsec.dsig_verify(doc, idp_cert)
   user = doc.find(".//saml:NameID", ns).text
   ```
   the two lines form an irresistibly intuitive mental sentence: *"Verify the document's signature, then read the user's NameID."* Nothing in that `2`-line surface reveals (a) that `dsig_verify` verified `<Extensions><Assertion ID="s1">` while `.find()` returned an unsigned `<Assertion ID="evil">` earlier in the same `doc`, nor (b) that `dsig_verify` stripped `<!--c-->` via `Exc-C14N` while `.text` stopped reading at `<!--c-->`! An API whose return type is `bool` (or `error` on an unmutated input `doc`, as in `xmlSecDSigCtxVerify`) **forces every human caller to reconstruct W3C C14N and XPath tree semantics in working memory**.
2. **Why `AppAuth-JS`'s `catch(() => undefined)` Is a Silent Comprehension Trap**:
   A developer passing `new AuthorizationRequest(json, crypto, /* usePkce = */ true)` reasonably believes PKCE is enforced; burying a silent fallback inside an internal `Promise.catch` turns an environmental deployment misconfiguration (e.g., testing or embedding over non-secure origin lacking `crypto.subtle`) into an invisible security downgrade.

#### 5.2 `(C2)` Conceptual Simplicity, Orthogonality & Universal Model Refinement
Across all four vulnerability families—SAML `XSW`/comments, OAuth `PKCE`/mix-up/`redirect_uri`, JWT `alg` confusion, and `CVE-2022-21449`—one overarching **Universal Parse-After-Verify Principle** collapses dozens of ad-hoc CVE mitigations into **three deep, minimal type invariants** (passing both Felleisen's non-encoding test and Ousterhout's interface-depth test):

1. **Cryptographic Verification as a Parser Constructor (`verify : RawBytes × VerifierCap<Alg, Key> -> Result<VerifiedPayload, Err>`, NEVER `Doc -> bool`)**:
   - Never parse untrusted wire bytes into a rich recursive AST (`XML DOM`, polymorphic JSON headers) *before* verifying authenticity, and never return `bool` over an input document.
   - Even for legacy SAML (`goxmldsig` `validate.go:363-370`), `verify` must consume `RawBytes`, enforce lossless token round-trip, verify `SignedInfo`, and construct its output **solely from the exact post-C14N `referencedBytes`** (`0` unverified wrapper nodes, `0` comment nodes!). For modern tokens (`PASETO` / typed `COSE`), pre-authentication framing uses canonical length-prefixed tuples (`PAE`) with **zero** attacker-controlled `"alg"` dispatch fields.
2. **Verifier-Pinned Algorithm & Key-Role Coupling (`VerifierCap<RS256, RsaPublicKey>`)**:
   - The verifier's static type fixes both the single permitted algorithm family and the matching key representation (`panva/jose` `prepareKey`), making `alg: "none"`, `RS256 -> HS256` HMAC confusion, and unpinned `jku`/`x5u` SSRF unrepresentable without runtime `WithValidMethods` checklists.
3. **Non-Zero Subgroup Types & Linear Flow-Session Capabilities (`PkceSession<S256, ExpectedIssuer, ExactRedirectUri>`)**:
   - Typing ECDSA scalars as `NonZeroMod<n>` (`1 <= x < n`) at byte-decoding boundary prevents Fermat `0^(n-2) == 0` bypasses (`CVE-2022-21449`), while reifying an initiated OAuth/OIDC request as a linear server/client session capability carrying `(S256Verifier, ExpectedIss, RegisteredRedirectUri)` statically forbids both `AppAuth-JS` fail-open `PKCE` omission and `FKS` cross-IdP code redemption!

---

## Boundaries

1. **SAML Encrypted Assertions (`<saml:EncryptedAssertion>` / `XML-Enc` `CBC` Padding Oracles, `not examined` in probe)**: When SAML combines `XML-Enc` (`AES-CBC` without MAC, `Kupser et al. CCS 2015`) with `XMLDSig` (*sign-then-encrypt* vs. *encrypt-then-sign*), adaptive chosen-ciphertext padding oracles and cross-recipient wrapping attacks arise even if `XSW` is fixed; `XML-Enc` decryption order was **not examined** in our execution probe.
2. **Post-Authentication Token Theft (`XSS` `localStorage` Extraction & Session-Cookie Replay, `known not to apply` to bearer verification alone)**: Even a mathematically sound `S256` `PKCE` + `RFC 9207` `iss` + `Ed25519` token pipeline does not protect bearer access tokens after issuance if stolen via browser XSS or reverse-proxy logs; sender-constrained proof-of-possession (`DPoP` `RFC 9449` or `mTLS` `RFC 8705`) is required to bind tokens to client key material (`referenced in RFC 9700`, `not examined` at library source level here).
3. **EdDSA (`Ed25519` `RFC 8032`) Cofactor-`8` Validation Subtlety (`known not to apply` identically to prime-order `CVE-2022-21449`)**: While `CVE-2022-21449` affects prime-order Weierstrass ECDSA (`P-256`/`P-384`/`P-521` in Java 15–18 via `s^(-1) = 0`), `Ed25519` avoids modular inversion during verification (`[8][S]B == [8]R + [8][k]A`)—where diverging implementations instead split on small-order torsion points, non-canonical `S >= L` malleability (`ZIP-215`), and batch vs. single verification equations.
4. **Legacy Non-`RFC 9207` OAuth 2.0 Authorization Servers (`unsupported` for `iss` parameter defense)**: Against legacy IdPs that omit `iss` on authorization responses (`authorization_response_iss_parameter_supported != true`), Relying Parties **must** fall back to distinct per-IdP `redirect_uri` endpoints (`FKS` countermeasure #2, `RFC 9700` §4.4.2.2) because `state` alone cannot distinguish `HIdP` redirects initiated via a `MITM`/`AIdP` mix-up.

---

## Evidence

| Subject / Artifact | Immutable Revision / Identifier | Verified Primary-Source Fact & Role |
| :--- | :--- | :--- |
| **`russellhaering/goxmldsig`** | Commit `10e2e6555035897cd38d90631553af153d2ffde6` (`validate.go:315-396, 495-565`) | Re-unmarshals `SignedInfo` strictly from `canonicalSignedInfoBytes` (`L318`), checks child cardinality in `validateShape` (`L384-395`), and re-parses `referencedBytes` into a fresh isolated `etree.Document` (`L363-370`). (`Basis: source`) |
| **`mattermost/xml-roundtrip-validator`** | Commit `3079e7b80fcab1eae8b64108e9157061b0cb4f35` (`validator.go:38-95`) | `Validate` / `ValidateAll` token-level Go `encoding/xml` round-trip mutation detector mitigating `CVE-2020-29509`..`29511`. (`Basis: source`) |
| **`lsh123/xmlsec`** | Commit `7469c2258e100afe7b42fcb8241d527fbf5898df` (`src/xmldsig.c:335-355`) | `xmlSecDSigCtxVerify(xmlSecDSigCtxPtr dsigCtx, xmlNodePtr node)` in-place status verification over `node->doc`, requiring caller-enforced verified-node reference checks. (`Basis: source`) |
| **`golang-jwt/jwt`** | Commit `f411663679b83c5b1005f8c54da427281de64680` (`parser.go:50-105`, `hmac.go:47-65`, `none.go:16-43`) | `p.validMethods` optional unless `WithValidMethods` passed (`parser.go:53`); `SigningMethodNone` globally registered in `init()` gated by `unsafeNoneMagicConstant` (`none.go:29`). (`Basis: source`) |
| **`panva/jose`** | Commit `d1e200f22d2bc66cd2ed6cc48fc622b6f1765cc5` (`src/lib/jws_verify.ts:115-195`, `src/lib/key.ts:11-90`) | `isDisjoint(protectedHeader, header)` (`L125`), `validateCrit` (`L131`), `"none"` absent from JWS algorithms, and `prepareKey` (`key.ts:43-90`) enforcing symmetric (`oct`/`secret`) vs. asymmetric (`public`) key-type separation. (`Basis: source`) |
| **`openid/AppAuth-JS`** | Commit `cbabdaf2747563cfac178e1aa89aa34c1c191d18` (`src/authorization_request.ts:75-115`) | `setupCodeVerifier()` `.catch(error => { log('Unable to generate PKCE challenge. Not using PKCE', error); return undefined; })` (`L95-98`) silently omitting `code_challenge` on WebCrypto error. (`Basis: source`) |
| **`openjdk/jdk`** | Commit `510deb132b0c5ff6fefdf7bde56d82223e927b69` (`src/java.base/share/classes/sun/security/ec/ECDSAOperations.java:215-232`) | Explicit `rb.signum() == 0 || sb.signum() == 0 || rb.compareTo(mod) >= 0 || sb.compareTo(mod) >= 0` (`L217-218`) ahead of Fermat `si.multiplicativeInverse()` (`L229`), fixing `CVE-2022-21449`. (`Basis: source`) |
| **Somorovsky et al. (2012)** | 21st USENIX Security Symposium (`2012`), *"On Breaking SAML: Be Whoever You Want to Be"* | Taxonomy of `XSW-1..8` attacks breaking `11/14` SAML SP stacks via verifier-consumer DOM mismatch. (`Basis: documentation`) |
| **Duo Labs (`CVE-2017-11427`..`11433`)** | CERT/CC `VU#475445` / Duo Labs Advisory (`2018-02-27`) | Non-comment `Exc-C14N` vs. first-text-node DOM extraction truncating `<NameID>` at `<!--comment-->`. (`Basis: normative + documentation`) |
| **Fett, Küsters & Schmitz (`CCS 2016` & `CSF 2017`)** | `DOI: 10.1145/2976749.2978385` (`arXiv:1601.01229`) & `arXiv:1704.08539` | Web Infrastructure Model (`WIM`) discovery of OAuth 2.0 / OIDC `IdP` Mix-Up and state/issuer-binding proofs. (`Basis: normative + documentation`) |
| **IETF `RFC 9700` & `RFC 8725`** | `BCP 240` (`RFC 9700`) & `BCP 225` (`RFC 8725`) | Normative mandates for universal `S256` `PKCE`, exact `redirect_uri` matching, `iss` mix-up defense, and JWT algorithm/key-type/URL validation. (`Basis: normative`) |
| **Executable Verification Probe** | `probes/verify_saml_oauth_jwt.py` (Python 3.10+ stdlib, observed `2026-11-19`) | Reproduced SAML `XSW` (`root@corp.example`) & stdlib `ElementTree` `CVE-2017-11427` comment truncation (`admin@corp.example`) vs. C14N isolated re-parse, `AppAuth-JS` PKCE fail-open & `redirect_uri` prefix bypass, `RS256->HS256` JWT forgery, and prime-curve `CVE-2022-21449` `(0, 0)` psychic ECDSA bypass. (`Basis: execution`) |

---

## Revalidation

1. **Run the preserved self-contained verification probe (`< 0.1 s`, Python 3.10+ standard library only)**:
   ```bash
   python3 reports/saml-xml-signature-wrapping-oauth-pkce-downgrades-and-jwt-confusion/probes/verify_saml_oauth_jwt.py
   ```
   Confirm `exit 0` and verify all assertions:
   ```text
   PASS: SAML XSW='root@corp.example', CommentTrunc='admin@corp.example' vs Safe='admin@corp.example.attacker.net' | OAuth prefix_bypass=True, RFC9700=False, AppAuth_PKCE_failopen=True | JWT RS256->HS256 vuln=True vs typed=False | CVE-2022-21449 (0,0) buggy=True vs fixed=False (valid_sig=True)
   ```
2. **Targeted upstream source revalidation checks on library upgrades**:
   - In `openid/AppAuth-JS`, inspect `src/authorization_request.ts` (`setupCodeVerifier`, `L90-108`) to determine whether `deriveChallenge(...).catch(...)` still resolves `undefined` (`fail-open`) when `usePkce == true` instead of rejecting the authorization request.
   - In `golang-jwt/jwt`, inspect `parser.go` (`NewParser` / `ParseWithClaims`) to see whether `WithValidMethods` becomes mandatory in future major versions (`v6+`) or whether `none.go` removes global `init()` registration of `SigningMethodNone`.
   - In `russellhaering/goxmldsig`, verify `validate.go` (`Validate` & `validateSignature`) continues running `rtvalidator.Validate` on raw XML input bytes and returning `doc.ReadFromBytes(referencedBytes)` rather than a mutated reference into the caller's input `etree.Element`.
