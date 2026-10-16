import json, sys
n = int(sys.argv[1]); control = sys.argv[2:] == ["control"]
code = bytes([0x61, n >> 8, n & 0xFF, 0x60, 0, 0x5B, 0x80, 0x60, 1, 0x01])
code += bytes([0x60, 0]) if control else bytes([0x81])
code += bytes([0x55, 0x60, 1, 0x01, 0x81, 0x81, 0x10, 0x60, 5, 0x57, 0x00])
addr, caller, code = "0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6", "0xcd1722f3947def4cf144679da39c4c32bdc35681", "0x" + code.hex()
acct = lambda storage: {addr: {"balance": "0x0de0b6b3a7640000", "code": code, "nonce": "0x00", "storage": storage}}
post = {"0x00": hex(n)} if control else {hex(i): hex(i + 1) for i in range(n)}
json.dump({"storeloop": {
    "env": {"currentCoinbase": "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba", "currentDifficulty": "0x0100",
            "currentGasLimit": "0x0f4240", "currentNumber": "0x00", "currentTimestamp": "0x01"},
    "exec": {"address": addr, "caller": caller, "code": code, "data": "0x", "gas": "0xe8d4a51000",
             "gasPrice": "0x5af3107a4000", "origin": caller, "value": "0x00"},
    "post": acct(post), "pre": acct({})}}, sys.stdout)
