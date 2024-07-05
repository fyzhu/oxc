mod atom;
mod misc;
mod parse;

pub use parse::PatternParser;

#[cfg(test)]
mod test {
    use crate::{ParserOptions, PatternParser};
    use oxc_allocator::Allocator;

    // NOTE: These may be useless when integlation tests are added
    #[test]
    fn should_pass() {
        let allocator = Allocator::default();

        for (source_text, options) in &[
            ("a", ParserOptions::default()),
            ("a+", ParserOptions::default()),
            ("a*", ParserOptions::default()),
            ("a?", ParserOptions::default()),
            ("a{1}", ParserOptions::default()),
            ("a{1,}", ParserOptions::default()),
            ("a{1,2}", ParserOptions::default()),
            ("a|b", ParserOptions::default()),
            ("a|b|c", ParserOptions::default()),
            ("a|b+?|c", ParserOptions::default()),
            ("a+b*?c{1}d{2,}e{3,4}?", ParserOptions::default()),
            (r"^(?=ab)\b(?!cd)(?<=ef)\B(?<!gh)$", ParserOptions::default()),
            ("a.b..", ParserOptions::default()),
            (r"\n\cM\0\x41\u1f60\.\/", ParserOptions::default()),
            (r"\u{1f600}", ParserOptions::default().with_unicode_flags(true, false)),
        ] {
            assert!(
                PatternParser::new(&allocator, source_text, *options).parse().is_ok(),
                "{source_text} should be parsed with {options:?}!",
            );
        }
    }

    #[test]
    fn should_fail() {
        let allocator = Allocator::default();

        for (source_text, options) in &[
            ("", ParserOptions::default()),
            ("a)", ParserOptions::default()),
            (r"b\", ParserOptions::default()),
            ("c]", ParserOptions::default()),
            ("d}", ParserOptions::default()),
            ("e|+", ParserOptions::default()),
            ("f|{", ParserOptions::default()),
            ("g{", ParserOptions::default()),
            ("g{1", ParserOptions::default()),
            ("g{1,", ParserOptions::default()),
            ("g{,", ParserOptions::default()),
            ("g{2,1}", ParserOptions::default()),
            ("(?=h", ParserOptions::default()),
            ("(?<!h", ParserOptions::default()),
            (r"\xi", ParserOptions::default()),
            (r"j\u{1f600}", ParserOptions::default()),
            (r"j\u", ParserOptions::default()),
        ] {
            assert!(
                PatternParser::new(&allocator, source_text, *options).parse().is_err(),
                "{source_text} should fail to parse with {options:?}!"
            );
        }
    }

    #[test]
    fn should_handle_unicode() {
        let allocator = Allocator::default();
        let source_text = "このEmoji🥹の数が変わる";

        let pattern =
            PatternParser::new(&allocator, source_text, ParserOptions::default()).parse().unwrap();
        assert_eq!(pattern.alternatives[0].elements.len(), 15);

        let pattern = PatternParser::new(
            &allocator,
            source_text,
            ParserOptions::default().with_unicode_flags(true, false),
        )
        .parse()
        .unwrap();
        assert_eq!(pattern.alternatives[0].elements.len(), 14);
        let pattern = PatternParser::new(
            &allocator,
            source_text,
            ParserOptions::default().with_unicode_flags(true, true),
        )
        .parse()
        .unwrap();
        assert_eq!(pattern.alternatives[0].elements.len(), 14);
    }
}
