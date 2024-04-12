#[derive(Debug, Clone, PartialEq, Hash)]
struct Loc(usize, usize);

impl Loc {
    fn merge(&mut self, other: &Loc) -> Loc {
        use std::cmp::{max, min};
        Loc(min(self.0, other.0), max(self.1, other.1))
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
struct Annot<T> {
    value: T,
    loc: Loc,
}

impl<T> Annot<T> {
    fn new(value: T, loc: Loc) -> Self {
        Self { value, loc }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Hash)]
enum TokenKind {
    Number(u64),
    Plus,
    Minus,
    Asterisk,
    Slash,
    LParen,
    RParen,
}

type Token = Annot<TokenKind>;

impl Token {
    fn number(n: u64, loc: Loc) -> Self {
        Self::new(TokenKind::Number(n), loc)
    }
    fn plus(loc: Loc) -> Self {
        Self::new(TokenKind::Plus, loc)
    }
    fn minus(loc: Loc) -> Self {
        Self::new(TokenKind::Minus, loc)
    }
    fn asterisk(loc: Loc) -> Self {
        Self::new(TokenKind::Asterisk, loc)
    }
    fn slash(loc: Loc) -> Self {
        Self::new(TokenKind::Slash, loc)
    }
    fn lparen(loc: Loc) -> Self {
        Self::new(TokenKind::LParen, loc)
    }
    fn rparen(loc: Loc) -> Self {
        Self::new(TokenKind::RParen, loc)
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
enum LexErrorKind {
    InvalidChar(char),
    Eof,
}

type LexError = Annot<LexErrorKind>;

impl LexError {
    fn invalid_char(c: char, loc: Loc) -> Self {
        Self::new(LexErrorKind::InvalidChar(c), loc)
    }
    fn eof(loc: Loc) -> Self {
        Self::new(LexErrorKind::Eof, loc)
    }
}

fn lex(input: &str) -> Result<Vec<Token>, LexError> {
    let mut tokens = Vec::new();
    let input = input.as_bytes();
    let mut pos = 0;
    macro_rules! lex_a_token {
        ($lexer:expr) => {{
            let (tok, p) = $lexer?;
            tokens.push(tok);
            pos = p;
        }};
    }
    while pos < input.len() {
        match input[pos] {
            b'0'..=b'9' => lex_a_token!(lex_number(input, pos)),
            b'+' => lex_a_token!(lex_plus(input, pos)),
            b'-' => lex_a_token!(lex_minus(input, pos)),
            b'*' => lex_a_token!(lex_asterisk(input, pos)),
            b'/' => lex_a_token!(lex_slash(input, pos)),
            b'(' => lex_a_token!(lex_lparen(input, pos)),
            b')' => lex_a_token!(lex_rparen(input, pos)),
            b' ' | b'\t' | b'\r' | b'\n' => {
                let ((), p) = skip_spaces(input, pos)?;
                pos = p;
            }
            b => return Err(LexError::invalid_char(b as char, Loc(pos, pos + 1))),
        }
    }
    Ok(tokens)
}

fn recognize_many(input: &[u8], mut pos: usize, mut f: impl FnMut(u8) -> bool) -> usize {
    while pos < input.len() && f(input[pos]) {
        pos += 1;
    }
    pos
}

fn consume_byte(input: &[u8], mut pos: usize, b: u8) -> Result<(u8, usize), LexError> {
    if input.len() <= pos {
        return Err(LexError::eof(Loc(pos, pos)));
    }
    if input[pos] != b {
        return Err(LexError::invalid_char(b as char, Loc(pos, pos + 1)));
    }
    pos += 1;
    Ok((b, pos))
}

fn skip_spaces(input: &[u8], mut pos: usize) -> Result<((), usize), LexError> {
    Ok(((), recognize_many(input, pos, |b| b" \r\n\t".contains(&b))))
}

fn lex_plus(input: &[u8], mut start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'+').map(|(_, end)| (Token::plus(Loc(start, end)), end))
}
fn lex_minus(input: &[u8], mut start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'-').map(|(_, end)| (Token::minus(Loc(start, end)), end))
}
fn lex_asterisk(input: &[u8], mut start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'*').map(|(_, end)| (Token::asterisk(Loc(start, end)), end))
}
fn lex_slash(input: &[u8], mut start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'/').map(|(_, end)| (Token::slash(Loc(start, end)), end))
}
fn lex_lparen(input: &[u8], mut start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b'(').map(|(_, end)| (Token::lparen(Loc(start, end)), end))
}
fn lex_rparen(input: &[u8], mut start: usize) -> Result<(Token, usize), LexError> {
    consume_byte(input, start, b')').map(|(_, end)| (Token::rparen(Loc(start, end)), end))
}

fn lex_number(input: &[u8], mut pos: usize) -> Result<(Token, usize), LexError> {
    use std::str::from_utf8;

    let start = pos;

    pos = recognize_many(input, pos, |b| b"1234567890".contains(&b));

    let n: u64 = from_utf8(&input[start..pos]).unwrap().parse().unwrap();
    Ok((Token::number(n, Loc(start, pos)), pos))
}

#[test]
fn test_lexer() {
    assert_eq!(lex("1"), Ok(vec![Token::number(1, Loc(0, 1))]));
    assert_eq!(lex("+"), Ok(vec![Token::plus(Loc(0, 1))]));
    assert_eq!(lex("\t\r\n 1"), Ok(vec![Token::number(1, Loc(4, 5))]));
    assert_eq!(lex("100"), Ok(vec![Token::number(100, Loc(0, 3))]));
    assert_eq!(
        lex("1+2-3*4/(5)"),
        Ok(vec![
            Token::number(1, Loc(0, 1)),
            Token::plus(Loc(1, 2)),
            Token::number(2, Loc(2, 3)),
            Token::minus(Loc(3, 4)),
            Token::number(3, Loc(4, 5)),
            Token::asterisk(Loc(5, 6)),
            Token::number(4, Loc(6, 7)),
            Token::slash(Loc(7, 8)),
            Token::lparen(Loc(8, 9)),
            Token::number(5, Loc(9, 10)),
            Token::rparen(Loc(10, 11)),
        ])
    );
}

fn main() {
    println!("Hello, parser!");
}
