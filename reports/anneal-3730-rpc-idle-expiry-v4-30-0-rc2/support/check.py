#!/usr/bin/env python3
"""Offline checker for retained pinned RPC idle-expiry result."""
import json
from pathlib import Path

r=json.loads((Path(__file__).resolve().parent/'results.json').read_text())
assert r['idle_seconds'] >= 42
assert r['wait'].get('result') == {}
assert 'result' in r['rich'] and 'result' in r['before']
assert r['expired'].get('error',{}).get('code') == -32900
assert r['new_connect']['result']['sessionId'] != r['connect']['result']['sessionId']
assert 'result' in r['recovered']
print('I044 RPC idle expiry retained result checks passed')
