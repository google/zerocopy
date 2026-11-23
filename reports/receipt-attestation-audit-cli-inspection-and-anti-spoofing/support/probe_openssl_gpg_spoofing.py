#!/usr/bin/env python3
"""Revalidate OpenSSL UTF-8 C1/Bidi escaping and GnuPG clearsigned framing."""

import os
import subprocess
import tempfile


def probe_openssl(td: str) -> None:
    cnf = os.path.join(td, "c.cnf")
    key = os.path.join(td, "k.pem")
    crt = os.path.join(td, "c.pem")

    # 1. ASCII C0 ESC in CN
    with open(cnf, "w", encoding="utf-8") as f:
        f.write("[req]\ndistinguished_name = dn\nprompt = no\n[dn]\nCN = EVIL\x1b[32mVERIFIED\x1b[0m\n")
    subprocess.check_call(
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", key, "-out", crt, "-days", "1", "-nodes", "-config", cnf],
        stderr=subprocess.DEVNULL,
    )
    out_c0 = subprocess.check_output(["openssl", "x509", "-in", crt, "-noout", "-subject"], text=True)
    print("openssl C0 -subject:", repr(out_c0))

    # 2. UTF-8 C1 CSI (U+009B) + Bidi RLO (U+202E) in CN
    with open(cnf, "wb") as f:
        f.write(b"[req]\nutf8 = yes\ndistinguished_name = dn\nprompt = no\n[dn]\nCN = EVIL\xc2\x9b32m_BIDI_\xe2\x80\xaefake\n")
    subprocess.check_call(
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", key, "-out", crt, "-days", "1", "-nodes", "-config", cnf],
        stderr=subprocess.DEVNULL,
    )
    out_utf8 = subprocess.check_output(["openssl", "x509", "-in", crt, "-noout", "-subject"], text=True)
    print("openssl UTF-8 C1/Bidi -subject:", repr(out_utf8))
    print("  raw_c1_csi_present:", "\x9b" in out_utf8)
    print("  raw_bidi_rlo_present:", "\u202e" in out_utf8)


def probe_gpg(td: str) -> None:
    env = os.environ.copy()
    gpghome = os.path.join(td, "gpghome")
    os.makedirs(gpghome, mode=0o700)
    env["GNUPGHOME"] = gpghome

    batch = os.path.join(td, "batch")
    with open(batch, "w", encoding="utf-8") as f:
        f.write("%no-protection\nKey-Type: eddsa\nKey-Curve: ed25519\nName-Real: Alice\n%commit\n")
    subprocess.check_call(["gpg", "--batch", "--gen-key", batch], env=env, stderr=subprocess.DEVNULL)

    msg = os.path.join(td, "msg.txt")
    sig = os.path.join(td, "msg.asc")
    spoof = os.path.join(td, "spoof.asc")
    verified_out = os.path.join(td, "verified.txt")

    with open(msg, "w", encoding="utf-8") as f:
        f.write("REAL SIGNED PAYLOAD\n")
    subprocess.check_call(["gpg", "--clearsign", "-o", sig, msg], env=env, stderr=subprocess.DEVNULL)

    with open(sig, encoding="utf-8") as f:
        signed_data = f.read()
    with open(spoof, "w", encoding="utf-8") as f:
        f.write("UNSIGNED HEADER SPOOF\n" + signed_data + "\nUNSIGNED TRAILER SPOOF\n")

    rv = subprocess.run(["gpg", "--status-fd=1", "--verify", spoof], env=env, capture_output=True, text=True)
    print("gpg --verify spoof exit:", rv.returncode)
    print("gpg --verify stderr:", repr(rv.stderr))
    rd = subprocess.run(["gpg", "--status-fd=2", "-o", verified_out, "--decrypt", spoof], env=env, capture_output=True, text=True)
    with open(verified_out, encoding="utf-8") as f:
        print("gpg --decrypt exit:", rd.returncode, "extracted:", repr(f.read()))


def main() -> None:
    with tempfile.TemporaryDirectory() as td:
        probe_openssl(td)
        probe_gpg(td)


if __name__ == "__main__":
    main()
