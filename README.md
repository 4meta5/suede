# suede

minimal DEX in sui-move

### implementation limitations

- sui-move does not support enums so it is necessary to define `swap_token_a` and `swap_token_b` even though they share code
- `struct Pool` requires `phantom` before token generics in order to compile
