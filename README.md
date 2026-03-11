# Yaspar

**Y**et **A**nother **S**MT **Pa**rser in **R**ust

A parsing library strictly following the [SMT-LIB 2.7](https://smt-lib.org/index.shtml)
standard, built on the [LALRPOP](https://github.com/lalrpop/lalrpop) parser generator.

## Architecture

Yaspar is composed of two stages:

1. **Tokenization** — `Tokenizer` consumes any `Iterator<Item = char>` and produces a stream
   of SMT-LIB tokens. Because it operates on a generic char iterator, it can efficiently
   tokenize from files, network streams, or in-memory strings without buffering the entire input.

2. **Parsing via callbacks** — The LALRPOP-generated parsers invoke trait methods on a
   user-supplied *action* object. Implement the trait hierarchy rooted at `ParsingAction` to
   receive callbacks for each syntactic construct (constants, identifiers, sorts, terms, and
   commands). If the token stream is grammatically malformed, the parser returns an error.

## Quick start

Add Yaspar to your `Cargo.toml`:

```toml
[dependencies]
yaspar = "2.7"
```

### Validate an SMT-LIB script

```rust
use yaspar::Parser;

let input = "(declare-const x Int)\n(assert (> x 0))\n(check-sat)";
assert!(Parser::new().parse(input).is_ok());
```

### Build a custom AST

Implement the callback traits (see the `action` module) and pass your action object to a
parser directly:

```rust
use yaspar::action::UnitAction;
use yaspar::{smtlib2, tokenize_str};

let input = "(assert (= x 1))";
let result = smtlib2::CommandParser::new()
    .parse(&mut UnitAction, tokenize_str(input, false));
assert!(result.is_ok());
```

### Block comments

SMT-LIB 2.7 introduces `#| ... |#` block comments. These are disabled by default for
backward compatibility. Enable them with:

```rust
use yaspar::Parser;

let parser = Parser::with_block_comments(true);
assert!(parser.parse("#| comment |# (check-sat)").is_ok());
```

## CLI

Yaspar ships with a small CLI for validating and benchmarking SMT-LIB files:

```bash
cargo run -- path/to/formula.smt2
# Parsed 42 commands in 3 ms
```

## Modules

| Module | Description |
|---|---|
| `action` | Callback traits and the no-op `UnitAction` reference implementation |
| `ast` | Data types for parsed values: keywords, sort/datatype/function declarations, grammar errors |
| `tokens` | The `Tokenizer` and the `Token` enum |
| `position` | Source location types (`Position` and `Range`) attached to every token and error |

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
