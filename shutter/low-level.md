# Opt-in Shutterized Gnosis Chain -- Low Level Specification

> :construction: :construction: :construction:
>
> This specification is a work in progress and not yet in effect.
>
> :construction: :construction: :construction:

This document is a specification of the first implementation phase of the Shutterized Beacon Chain proposal. It is intended to be implemented on Gnosis Chain.

For an overview over the protocol, rationale, and security discussion, checkout the [high-level document](shutter/high-level.md).

## Applications

This section describes the functionality of the applications involved in the protocol.

### Keyper

> :construction: :construction: :construction:
>
> Todo
>
> :construction: :construction: :construction:

msg format:

```
message Key {
        bytes identity = 1;
        bytes key = 2;
}

message DecryptionKeys {
    uint64 instanceID = 1;
    uint64 eon = 2;
    uint64 blockNumber = 3;
    repeated Key keys = 4;
    repeated uint64 signerIndices = 5;
    repeated bytes signatures = 6;
}
```

`DecryptionKeys` is considered valid, under given instance id and chain status, if:

- instance id is correct
- eon is correct
- signer indices is ordered ascending, does not contain repeats, and are valid indices of keyper set given by eon
- signatures has same size as `signerIndices`
- each signature is a valid ECDSA signature by the corresponding keyper given by `signerIndices` of the following message:
  - `keccak256(instance ID | eon | blockNumber | keccak256(epochs))`

### Validator

Validators should keep track if they are a registered in the Validator Registry, i.e., `validator_index in compute_participating_validators(state, events)` where

- `validator_index` is the index of the validator in the Beacon Chain,
- `state` is the current Beacon Chain state, and
- `events` are the events emitted by the Validator Registry according to `state` in ascending order.

Registered validators subscribe to `DecryptionKeys` messages from keypers on the topic `tbd` and validate them as described [above](tbd).

If a registered validator is selected as the block proposer for slot `s`, they hold off on producing a block until they receive a valid `DecryptionKeys` message `m` where `m.blockNumber` is the incremented number of the head block at the beginning of `s`. If no such message is received up until the end of `s`, the proposer proposes no block.

Once `m` is received, the validator fetches those `TransactionSubmitted` events `e` from the sequencer contract that, for any `k` in `m.keys`, fulfill

- `e.args.eon == m.eon` and
- `compute_identity(e.args.identityPrefix, e.sender) == k.identity`.

For each `e` with corresponding `k`, the validator first computes `encrypted_transaction = decode_encrypted_message(e.encryptedTransaction)` and then `decrypted_transaction = decrypt(encrypted_transaction, k.key)`. If any of the functions fails, they skip `e`.

With the set of decrypted transactions `decrypted_transactions`, the validator constructs a block `b` such that the first transactions are a subset of `decrypted_transactions`. The transactions are in the correct order, i.e., taking any two decrypted transactions from the block at indices `i1` and `i2 > i1`, the corresponding indices in `decrypted_transactions` `j1` and `j2` fulfill `j2 > j1`. Furthermore, for any decrypted transaction that is missing in the block, inserting it in accordance with the ordering property and removing all following transactions would make the block invalid.

### Encrypting RPC Server

> :construction: :construction: :construction:
>
> Todo
>
> :construction: :construction: :construction:

### Decryption Key Relay

> :construction: :construction: :construction:
>
> Todo
>
> :construction: :construction: :construction:

## Smart Contracts

This section specifies the interfaces and behavior of the smart contracts in the protocol. The id of the chain on which they are deployed is `CHAIN_ID`.

### Sequencer

The Sequencer is a contract deployed at address `SEQUENCER_ADDRESS`. It implements the following interface:

```Solidity
interface ISequencer {
    function submitEncryptedTransaction(uint64 eon, bytes32 identityPrefix, address sender, bytes calldata encryptedTransaction, uint256 gasLimit) external;

    event TransactionSubmitted(uint64 eon, bytes32 identityPrefix, address sender, bytes encryptedTransaction, uint256 gasLimit);
}
```

`submitEncryptedTransaction(eon, identityPrefix, encryptedTransaction, gasLimit)` reverts if `msg.value < block.baseFee * gasLimit`. Otherwise, it emits the event `TransactionSubmitted(eon, msg.sender, identityPrefix, encryptedTransaction, gasLimit)`.

### Validator Registry

The Validator Registry is a contract deployed at address `VALIDATOR_REGISTRY_ADDRESS`. It implements the following interface:

```
interface IValidatorRegistry {
    function register(bytes memory registrationMessage, bytes memory registrationSignature) external;
    function deregister(bytes memory deregistrationMessage, bytes memory deregistrationSignature) external;

    event Registration(bytes registrationMessage, bytes registrationSignature);
    event Deregistration(bytes deregistrationMessage, bytes deregistrationSignature);
}
```

`register(registrationMessage, registrationSignature)` emits the event `Registration(registrationMessage, registrationSignature)`.

`deregister(deregistrationMessage, deregistrationSignature)` emits the event `Deregistration(deregistrationMessage, deregistrationSignature)`.

In order to announce their intent to start or stop participating in the protocol, validators call `register(message, signature)` or `deregister(message, signature)`, respectively. `message` is computed by `compute_registration_message` or `compute_deregistration_message`, respectively:

```Python
def compute_registration_message(validator_index: uint64, nonce: uint64):
    return compute_registry_message_prefix(validator_index, nonce) + "_registration"

def compute_deregistration_message(validator_index: uint64, nonce: uint64):
    return compute_registry_message_prefix(validator_index, nonce) + "_deregistration"

def compute_registry_message_prefix(validator_index: uint64, nonce: uint64):
    return VALIDATOR_REGISTRY_MESSAGE_VERSION + CHAIN_ID.to_bytes(8, "big") + VALIDATOR_REGISTRY_ADDRESS + validator_index.to_bytes(8, "big") + nonce.to_bytes(8, "big")
```

The parameters are as follows:

- `validator_index` is the Beacon Chain index of the registering or deregistering validator.
- `nonce` is a `uint64` greater than the nonce used in any previously published registration or deregistration message by the registering validator.
- `VALIDATOR_REGISTRY_MESSAGE_VERSION = b"\x00"`

`signature = bls.Sign(validator_privkey, keccak256(message))` where `validator_privkey` is the private key of the validator.

The list of indices of all participating validators is `compute_participating_validators(state, events)`, given the beacon chain state `state` and the set of events `events` emitted by the Validator Registry in ascending order of emission:

```Python
def compute_participating_validators(state, events) -> Sequence[ValidatorIndex]:
    indices = set()
    prev_nonces = {}

    for event in events:
        if event.name == "Registration":
            is_registration_event = True
            message = event.args.registrationMessage
            signature = event.args.registrationSignature
        elif event.name == "Deregistration":
            is_registration_event = False
            message = event.args.deregistrationMessage
            signature = event.args.deregistrationSignature
        else:
            assert False

        try:
            (
                version,
                chain_id,
                validator_registry_address,
                validator_index,
                nonce,
                is_registration,
            ) = extract_message_parts(event.args.message)
        except:
            continue

        if is_registration_event != is_registration:
            continue

        if version != VALIDATOR_REGISTRY_MESSAGE_VERSION:
            continue
        if chain_id != CHAIN_ID:
            continue
        if validator_registry_address != VALIDATOR_REGISTRY_ADDRESS:
            continue

        if validator_index >= len(state.validators):
            continue
        if nonce <= prev_nonces.get(validator_index, -1):
            continue

        validator_pubkey = state.validators[validator_index].pubkey
        if !bls.Verify(validator_pubkey, keccak256(message), signature):
            continue

        prev_nonces[validator_index] = nonce
        if is_registration:
            indices.add(validator_index)
        else:
            indices.remove(validator_index)

    return sorted(indices)

def extract_message_parts(message: bytes) -> Tuple[bytes, uint64, Address, uint64, uint64, bool]:
    prefix_and_suffix = message.split("_")
    assert len(prefix_and_suffix) == 2
    prefx, suffix = prefix_and_suffix

    if suffix == "registration":
        is_registration = True
    elif suffix == "deregistration":
        is_registration = False

    assert len(prefix) == 1 + 8 + 20 + 8 + 8
    version = prefix[0]
    chain_id_bytes = prefix[1:9]
    registry_address = prefix[9:29]
    index_bytes = prefix[29:37]
    nonce_bytes = prefix[37:45]

    chain_id = int.from_bytes(chain_id_bytes, "big")
    index = int.from_bytes(index_bytes, "big")
    nonce = int.from_bytes(nonce_bytes, "big")

    return version, chain_id, registry_address, index, nonce, is_registration
```

### Key Broadcast Contract

The Key Broadcast Contract is deployed at address `KEY_BROADCAST_CONTRACT_ADDRESS`. It implements the following interface:

```
interface IKeyBroadcastContract {
    function broadcastEonKey(uint64 eon, bytes memory key) external;
    function getEonKey(uint64 eon) external view returns (bytes memory);

    event EonKeyBroadcast(uint64 eon, bytes key)
}
```

`broadcastEonKey(eon, key)` reverts if any of the following conditions is met at the time of the call:

1. The contract has already stored a key for the given eon.
2. `key` is empty.
3. `IKeyperSetManager(KEYPER_SET_MANAGER_MANAGER_ADDRESS).getKeyperSetAddress(eon)` reverts or returns an address different from `msg.sender`.

Otherwise, it stores `key` in a way that it is indexable by `eon` and emits the event `EonKeyBroadcast(eon, key)`.

`getEonKey(eon)` returns the key stored for `eon`, or an empty bytes value if no key for `eon` is stored.

### Keyper Set Manager

The Keyper Set Manager is a contract deployed at address `KEYPER_SET_MANAGER_ADDRESS`. It implements the following interface:

```
interface IKeyperSetManager {
    function addKeyperSet(uint64 activationSlot, address keyperSetContract) external;
    function getNumKeyperSets() external view returns (uint64);
    function getKeyperSetIndexBySlot(uint64 slot) external view returns (address, uint64);
    function getKeyperSetAddress(uint64 index) external view returns (address, uint64);
    function getKeyperSetActivationSlot(uint64 index) external view returns (uint64);

    event KeyperSetAdded(uint64 activationSlot, address keyperSetContract);
}
```

In addition, the contract implements the [Contract Ownership Standard (ERC-173)](https://eips.ethereum.org/EIPS/eip-173).

`addKeyperSet(activationSlot, keyperSetContract)` reverts if any one of the following conditions is met at the time of the call:

1. `msg.sender != owner()`
2. `getNumKeyperSets() > 0 && activationSlot < getKeyperSetActivationSlot(getNumKeyperSets() - 1)`

Otherwise, `addKeyperSet` saves `keyperSetContract` and the corresponding `activationSlot` to storage. Finally, it emits the event `KeyperSetAdded(activationSlot, keyperSetContract)`.

Define

- `n` as the number of added keyper sets,
- `k_0 ... k_(n - 1)` as the keyper sets in the order they were added, and
- `s_0 ... s_(n - 1)` as the corresponding activation slot numbers.

Then, there are `n` eons `e_i` starting at slot `s_i` (inclusive). Eon `e_i` for `i = 0 ... n - 2` ends at slot `s_(i + 1)` (exclusive), eon `e_(n - 1)` is tentatively open ended. The keyper set for any slot in `e_i` is `k_i`.

`getNumKeyperSets()` returns `n`.

`getKeyperSetIndexBySlot(s)` reverts if `n == 0` or `s < s_0`. Otherwise, it returns `k_i` where `i` is the index of the eon that contains slot `s`.

`getKeyperSetAddress(i)` reverts if `i >= n`. Otherwise, it returns `k_i`.

`getKeyperSetActivationSlot(i)` reverts if `i >= n`. Otherwise, it returns `s_i`.

### Keyper Set Contract

Keyper set contracts are contracts which fulfill the following interface:

```
interface IKeyperSet {
    function isFinalized() external view returns (bool);
    function getNumMembers() external view returns (uint64);
    function getMember(uint64 index) external view returns (address);
    function getMembers() external view returns (address[] memory);
    function getThreshold() external view returns (uint64);
}
```

If `isFinalized` returns `false`, the behavior of the contract is unspecified. If `isFinalized()` returns `true`:

- `getNumMembers()` returns a number `n` that is greater than or equal to `1`.
- `getMembers()` returns an array of `n` non-zero addresses.
- `getMember(i)` returns `getMembers()[i]` for `0 <= i < n` and the zero address for `i >= n`.
- `getThreshold()` returns a number `t` with `1 <= t <= n`.
- The return values of `isFinalized`, `getNumMembers`, `getMember`, `getMembers`, and `getThreshold` will not change in the future.

## Cryptography

This section defines the cryptographic primitives used in the protocol.

### Definitions

| Type                                            | Description                                                                                                                      |
| ----------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------- |
| G1                                              | An element of the BN256-group G1 as defined in [EIP-197](https://eips.ethereum.org/EIPS/eip-197#definition-of-the-groups)        |
| G2                                              | An element of the BN256-group G2 as defined in [EIP-197](https://eips.ethereum.org/EIPS/eip-197#definition-of-the-groups)        |
| GT                                              | An element of the BN256-group GT, the range of the pairing function defined in [EIP-197](https://eips.ethereum.org/EIPS/eip-197) |
| Block                                           | A 32-byte block                                                                                                                  |
| EncryptedMessage = (G2, Block, Sequence[Block]) | An encrypted message                                                                                                             |

| Constant | Description                   | Value                                                                         |
| -------- | ----------------------------- | ----------------------------------------------------------------------------- |
| ORDER    | The order of groups G1 and G2 | 21888242871839275222246405745257275088548364400416034343698204186575808495617 |

The following functions are considered prerequisites:

| Function                       | Description                                                                                     |
| ------------------------------ | ----------------------------------------------------------------------------------------------- |
| keccak256(bytes) -> Block      | The keccak-256 hash function                                                                    |
| pairing(G1, G2) -> GT          | The pairing function specified in [EIP-197](https://eips.ethereum.org/EIPS/eip-197)             |
| g1_scalar_base_mult(int) -> G1 | Multiply the generator of G1 by a scalar                                                        |
| g2_scalar_base_mult(int) -> G2 | Multiply the generator of G2 by a scalar                                                        |
| gt_scalar_mult(GT, int)        | Multiply an element of GT by a scalar                                                           |
| encode_g1(G1) -> bytes         | Encode an element of G1 according to [EIP-197](https://eips.ethereum.org/EIPS/eip-197#encoding) |
| encode_g2(G2) -> bytes         | Encode an element of G2 according to [EIP-197](https://eips.ethereum.org/EIPS/eip-197#encoding) |
| decode_g2(bytes) -> G2         | Decode an element of G2 according to [EIP-197](https://eips.ethereum.org/EIPS/eip-197#encoding) |

### Helper Functions

```Python
def hash_block_to_int(block: Block) -> int:
    h = keccak256(block)
    i = int.from_bytes(h, "big")
    return i % ORDER

def hash_gt_to_block(preimage: GT) -> Block:
    b = encode_gt(preimage)
    return hash_bytes_to_block(b)

def hash_bytes_to_block(preimage: bytes) -> Block:
    return keccak256(preimage)

def encode_gt(value: GT) -> bytes:
    pass  # TODO

def xor_blocks(block1: Block, block2: Block) -> Block:
    return Block(bytes(b1 ^ b2 for b1, b2 in zip(block1, block2)))

def pad_and_split(b: bytes) -> Sequence[Block]:
    # pad according to PKCS #7
    n = 32 - len(b) % 32
    padded = b + n * bytes([n])
    return [padded[i:i + 32] for i in range(0, len(padded), 32)]

def unpad_and_join(blocks: Sequence[Block]) -> bytes:
    # unpad according to PKCS #7
    if len(blocks) == 0:
        return b""
    last_block = blocks[-1]
    n = last_block[-1]
    assert 0 < n <= 32, "invalid padding length"
    return b"".join(blocks)[:-n]

def compute_block_keys(sigma: Block, n: int) -> Sequence[Block]:
    suffix_length = max(n.bit_length() + 7) // 8, 1)
    suffixes = [n.to_bytes(suffix_length, "big")]
    preimages = [sigma + suffix for suffix in suffixes]
    keys = [hash_bytes_to_block(preimage) for preimage in preimages]
    return keys
```

### Encryption and Decryption

```Python
def encrypt(message: bytes, identity: G1, eon_key: G2, sigma: Block) -> EncryptedMessage:
    message_blocks = pad_and_split(message)
    r = compute_r(sigma)
    return (
        compute_c1(r),
        compute_c2(sigma, r, identity, eon_key),
        compute_c3(message_blocks, sigma),
    )

def compute_r(sigma: Block) -> int:
    return hash_block_to_int(sigma)

def compute_c1(r: int) -> G2:
    return g2_scalar_base_mult(r)

def compute_c2(sigma: Block, r: int, identity: G1, eon_key: G2) -> Block:
    p = pairing(identity, eon_key)
    preimage = gt_scalar_mult(p, r)
    key = hash_gt_to_block(preimage)
    return xor_blocks(sigma, key)

def compute_c3(message_blocks: Sequence[Block], sigma: Block) -> Sequence[Block]:
    keys = compute_block_keys(sigma, len(message_blocks))
    return [xor_blocks(key, block) for key, block in zip(keys, blocks)]

def compute_identity(prefix: bytes, sender: bytes) -> G1:
    h = keccak256(prefix + sender)
    i = int.from_bytes(h, "big")
    return g1_scalar_base_mult(i)
```

```Python
def decrypt(encrypted_message: EncryptedMessage, decryption_key: G1) -> bytes:
    sigma = recover_sigma(encrypted_message, decryption_key)
    _, _, c3 = encrypted_message
    keys = compute_block_keys(sigma, len(blocks))
    decrypted_blocks = [xor_blocks(key, block) for key, block in zip(keys, blocks)]
    return unpad_and_join(decrypted_blocks)

def recover_sigma(encrypted_message: EncryptedMessage, decryption_key: G1) -> Block:
    c1, c2, _ = encrypted_message
    p = pairing(decryption_key, c1)
    key = hash_gt_to_block(p)
    sigma = xor_blocks(c2, decryption_key)
    return sigma
```

### Encoding

```Python
def encode_decryption_key(decryption_key: G1) -> bytes:
    return encode_g1(decryption_key)

def encode_decryption_key_share(decryption_key_share: G1) -> bytes:
    return encode_g1(k)

def encode_encrypted_message(encrypted_message: EncryptedMessage) -> bytes:
    c1, c2, c3 = encrypted_message
    return encode_g2(c1) + c2 + b"".join(c3)

def decode_encrypted_message(b: bytes) -> EncryptedMessage:
    assert len(b) > 4 * 32 + 32 + 32
    c1_bytes = b[:4 * 32]
    c2 = b[4 * 32: 5 * 32]
    c3_bytes = b[5 * 32:]
    c1 = decode_g2(c1_bytes)
    assert len(c3_bytes) % 32 == 0
    c3 = [c3_bytes[i:i + 32] for i in range(0, len(c3_bytes), 32)]
    return (c1, c2, c3)
```
