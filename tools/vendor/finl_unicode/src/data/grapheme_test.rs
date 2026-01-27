// GENERATED CODE DO NOT MANUALLY EDIT

use crate::grapheme_clusters::tests::grapheme_test;

#[test]
fn standard_grapheme_test() {
	grapheme_test("\u{000D}\u{000D}",
		&["\u{000D}", "\u{000D}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{000D}",
		&["\u{000D}", "\u{0308}", "\u{000D}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{000A}",
		&["\u{000D}\u{000A}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) × [3.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{000A}",
		&["\u{000D}", "\u{0308}", "\u{000A}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0000}",
		&["\u{000D}", "\u{0000}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{0000}",
		&["\u{000D}", "\u{0308}", "\u{0000}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{094D}",
		&["\u{000D}", "\u{094D}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{094D}",
		&["\u{000D}", "\u{0308}\u{094D}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0300}",
		&["\u{000D}", "\u{0300}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{0300}",
		&["\u{000D}", "\u{0308}\u{0300}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{200C}",
		&["\u{000D}", "\u{200C}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{200C}",
		&["\u{000D}", "\u{0308}\u{200C}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{200D}",
		&["\u{000D}", "\u{200D}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{200D}",
		&["\u{000D}", "\u{0308}\u{200D}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{1F1E6}",
		&["\u{000D}", "\u{1F1E6}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{1F1E6}",
		&["\u{000D}", "\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{06DD}",
		&["\u{000D}", "\u{06DD}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{06DD}",
		&["\u{000D}", "\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0903}",
		&["\u{000D}", "\u{0903}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{0903}",
		&["\u{000D}", "\u{0308}\u{0903}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{1100}",
		&["\u{000D}", "\u{1100}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{1100}",
		&["\u{000D}", "\u{0308}", "\u{1100}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{1160}",
		&["\u{000D}", "\u{1160}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{1160}",
		&["\u{000D}", "\u{0308}", "\u{1160}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{11A8}",
		&["\u{000D}", "\u{11A8}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{11A8}",
		&["\u{000D}", "\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{AC00}",
		&["\u{000D}", "\u{AC00}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{AC00}",
		&["\u{000D}", "\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{AC01}",
		&["\u{000D}", "\u{AC01}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{AC01}",
		&["\u{000D}", "\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0915}",
		&["\u{000D}", "\u{0915}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{0915}",
		&["\u{000D}", "\u{0308}", "\u{0915}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{00A9}",
		&["\u{000D}", "\u{00A9}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{00A9}",
		&["\u{000D}", "\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0020}",
		&["\u{000D}", "\u{0020}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{0020}",
		&["\u{000D}", "\u{0308}", "\u{0020}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0378}",
		&["\u{000D}", "\u{0378}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{0308}\u{0378}",
		&["\u{000D}", "\u{0308}", "\u{0378}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{000D}",
		&["\u{000A}", "\u{000D}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{000D}",
		&["\u{000A}", "\u{0308}", "\u{000D}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{000A}",
		&["\u{000A}", "\u{000A}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{000A}",
		&["\u{000A}", "\u{0308}", "\u{000A}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0000}",
		&["\u{000A}", "\u{0000}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{0000}",
		&["\u{000A}", "\u{0308}", "\u{0000}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{094D}",
		&["\u{000A}", "\u{094D}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{094D}",
		&["\u{000A}", "\u{0308}\u{094D}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0300}",
		&["\u{000A}", "\u{0300}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{0300}",
		&["\u{000A}", "\u{0308}\u{0300}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{200C}",
		&["\u{000A}", "\u{200C}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{200C}",
		&["\u{000A}", "\u{0308}\u{200C}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{200D}",
		&["\u{000A}", "\u{200D}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{200D}",
		&["\u{000A}", "\u{0308}\u{200D}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{1F1E6}",
		&["\u{000A}", "\u{1F1E6}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{1F1E6}",
		&["\u{000A}", "\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{06DD}",
		&["\u{000A}", "\u{06DD}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{06DD}",
		&["\u{000A}", "\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0903}",
		&["\u{000A}", "\u{0903}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{0903}",
		&["\u{000A}", "\u{0308}\u{0903}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{1100}",
		&["\u{000A}", "\u{1100}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{1100}",
		&["\u{000A}", "\u{0308}", "\u{1100}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{1160}",
		&["\u{000A}", "\u{1160}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{1160}",
		&["\u{000A}", "\u{0308}", "\u{1160}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{11A8}",
		&["\u{000A}", "\u{11A8}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{11A8}",
		&["\u{000A}", "\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{AC00}",
		&["\u{000A}", "\u{AC00}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{AC00}",
		&["\u{000A}", "\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{AC01}",
		&["\u{000A}", "\u{AC01}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{AC01}",
		&["\u{000A}", "\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0915}",
		&["\u{000A}", "\u{0915}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{0915}",
		&["\u{000A}", "\u{0308}", "\u{0915}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{00A9}",
		&["\u{000A}", "\u{00A9}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{00A9}",
		&["\u{000A}", "\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0020}",
		&["\u{000A}", "\u{0020}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{0020}",
		&["\u{000A}", "\u{0308}", "\u{0020}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0378}",
		&["\u{000A}", "\u{0378}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000A}\u{0308}\u{0378}",
		&["\u{000A}", "\u{0308}", "\u{0378}"],
		"  ÷ [0.2] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{000D}",
		&["\u{0000}", "\u{000D}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{000D}",
		&["\u{0000}", "\u{0308}", "\u{000D}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{000A}",
		&["\u{0000}", "\u{000A}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{000A}",
		&["\u{0000}", "\u{0308}", "\u{000A}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0000}",
		&["\u{0000}", "\u{0000}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{0000}",
		&["\u{0000}", "\u{0308}", "\u{0000}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{094D}",
		&["\u{0000}", "\u{094D}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{094D}",
		&["\u{0000}", "\u{0308}\u{094D}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0300}",
		&["\u{0000}", "\u{0300}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{0300}",
		&["\u{0000}", "\u{0308}\u{0300}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{200C}",
		&["\u{0000}", "\u{200C}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{200C}",
		&["\u{0000}", "\u{0308}\u{200C}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{200D}",
		&["\u{0000}", "\u{200D}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{200D}",
		&["\u{0000}", "\u{0308}\u{200D}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{1F1E6}",
		&["\u{0000}", "\u{1F1E6}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{1F1E6}",
		&["\u{0000}", "\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{06DD}",
		&["\u{0000}", "\u{06DD}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{06DD}",
		&["\u{0000}", "\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0903}",
		&["\u{0000}", "\u{0903}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{0903}",
		&["\u{0000}", "\u{0308}\u{0903}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{1100}",
		&["\u{0000}", "\u{1100}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{1100}",
		&["\u{0000}", "\u{0308}", "\u{1100}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{1160}",
		&["\u{0000}", "\u{1160}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{1160}",
		&["\u{0000}", "\u{0308}", "\u{1160}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{11A8}",
		&["\u{0000}", "\u{11A8}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{11A8}",
		&["\u{0000}", "\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{AC00}",
		&["\u{0000}", "\u{AC00}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{AC00}",
		&["\u{0000}", "\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{AC01}",
		&["\u{0000}", "\u{AC01}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{AC01}",
		&["\u{0000}", "\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0915}",
		&["\u{0000}", "\u{0915}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{0915}",
		&["\u{0000}", "\u{0308}", "\u{0915}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{00A9}",
		&["\u{0000}", "\u{00A9}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{00A9}",
		&["\u{0000}", "\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0020}",
		&["\u{0000}", "\u{0020}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{0020}",
		&["\u{0000}", "\u{0308}", "\u{0020}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0378}",
		&["\u{0000}", "\u{0378}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0000}\u{0308}\u{0378}",
		&["\u{0000}", "\u{0308}", "\u{0378}"],
		"  ÷ [0.2] <NULL> (Control) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{000D}",
		&["\u{094D}", "\u{000D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{000D}",
		&["\u{094D}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{000A}",
		&["\u{094D}", "\u{000A}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{000A}",
		&["\u{094D}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0000}",
		&["\u{094D}", "\u{0000}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{0000}",
		&["\u{094D}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{094D}",
		&["\u{094D}\u{094D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{094D}",
		&["\u{094D}\u{0308}\u{094D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0300}",
		&["\u{094D}\u{0300}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{0300}",
		&["\u{094D}\u{0308}\u{0300}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{200C}",
		&["\u{094D}\u{200C}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{200C}",
		&["\u{094D}\u{0308}\u{200C}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{200D}",
		&["\u{094D}\u{200D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{200D}",
		&["\u{094D}\u{0308}\u{200D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{1F1E6}",
		&["\u{094D}", "\u{1F1E6}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{1F1E6}",
		&["\u{094D}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{06DD}",
		&["\u{094D}", "\u{06DD}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{06DD}",
		&["\u{094D}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0903}",
		&["\u{094D}\u{0903}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{0903}",
		&["\u{094D}\u{0308}\u{0903}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{1100}",
		&["\u{094D}", "\u{1100}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{1100}",
		&["\u{094D}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{1160}",
		&["\u{094D}", "\u{1160}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{1160}",
		&["\u{094D}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{11A8}",
		&["\u{094D}", "\u{11A8}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{11A8}",
		&["\u{094D}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{AC00}",
		&["\u{094D}", "\u{AC00}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{AC00}",
		&["\u{094D}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{AC01}",
		&["\u{094D}", "\u{AC01}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{AC01}",
		&["\u{094D}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0915}",
		&["\u{094D}", "\u{0915}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{0915}",
		&["\u{094D}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{00A9}",
		&["\u{094D}", "\u{00A9}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{00A9}",
		&["\u{094D}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0020}",
		&["\u{094D}", "\u{0020}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{0020}",
		&["\u{094D}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0378}",
		&["\u{094D}", "\u{0378}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{094D}\u{0308}\u{0378}",
		&["\u{094D}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{000D}",
		&["\u{0300}", "\u{000D}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{000D}",
		&["\u{0300}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{000A}",
		&["\u{0300}", "\u{000A}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{000A}",
		&["\u{0300}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0000}",
		&["\u{0300}", "\u{0000}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{0000}",
		&["\u{0300}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{094D}",
		&["\u{0300}\u{094D}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{094D}",
		&["\u{0300}\u{0308}\u{094D}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0300}",
		&["\u{0300}\u{0300}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{0300}",
		&["\u{0300}\u{0308}\u{0300}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{200C}",
		&["\u{0300}\u{200C}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{200C}",
		&["\u{0300}\u{0308}\u{200C}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{200D}",
		&["\u{0300}\u{200D}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{200D}",
		&["\u{0300}\u{0308}\u{200D}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{1F1E6}",
		&["\u{0300}", "\u{1F1E6}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{1F1E6}",
		&["\u{0300}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{06DD}",
		&["\u{0300}", "\u{06DD}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{06DD}",
		&["\u{0300}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0903}",
		&["\u{0300}\u{0903}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{0903}",
		&["\u{0300}\u{0308}\u{0903}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{1100}",
		&["\u{0300}", "\u{1100}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{1100}",
		&["\u{0300}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{1160}",
		&["\u{0300}", "\u{1160}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{1160}",
		&["\u{0300}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{11A8}",
		&["\u{0300}", "\u{11A8}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{11A8}",
		&["\u{0300}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{AC00}",
		&["\u{0300}", "\u{AC00}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{AC00}",
		&["\u{0300}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{AC01}",
		&["\u{0300}", "\u{AC01}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{AC01}",
		&["\u{0300}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0915}",
		&["\u{0300}", "\u{0915}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{0915}",
		&["\u{0300}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{00A9}",
		&["\u{0300}", "\u{00A9}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{00A9}",
		&["\u{0300}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0020}",
		&["\u{0300}", "\u{0020}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{0020}",
		&["\u{0300}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0378}",
		&["\u{0300}", "\u{0378}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0300}\u{0308}\u{0378}",
		&["\u{0300}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{000D}",
		&["\u{200C}", "\u{000D}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{000D}",
		&["\u{200C}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{000A}",
		&["\u{200C}", "\u{000A}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{000A}",
		&["\u{200C}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0000}",
		&["\u{200C}", "\u{0000}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{0000}",
		&["\u{200C}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{094D}",
		&["\u{200C}\u{094D}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{094D}",
		&["\u{200C}\u{0308}\u{094D}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0300}",
		&["\u{200C}\u{0300}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{0300}",
		&["\u{200C}\u{0308}\u{0300}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{200C}",
		&["\u{200C}\u{200C}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{200C}",
		&["\u{200C}\u{0308}\u{200C}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{200D}",
		&["\u{200C}\u{200D}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{200D}",
		&["\u{200C}\u{0308}\u{200D}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{1F1E6}",
		&["\u{200C}", "\u{1F1E6}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{1F1E6}",
		&["\u{200C}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{06DD}",
		&["\u{200C}", "\u{06DD}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{06DD}",
		&["\u{200C}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0903}",
		&["\u{200C}\u{0903}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{0903}",
		&["\u{200C}\u{0308}\u{0903}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{1100}",
		&["\u{200C}", "\u{1100}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{1100}",
		&["\u{200C}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{1160}",
		&["\u{200C}", "\u{1160}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{1160}",
		&["\u{200C}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{11A8}",
		&["\u{200C}", "\u{11A8}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{11A8}",
		&["\u{200C}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{AC00}",
		&["\u{200C}", "\u{AC00}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{AC00}",
		&["\u{200C}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{AC01}",
		&["\u{200C}", "\u{AC01}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{AC01}",
		&["\u{200C}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0915}",
		&["\u{200C}", "\u{0915}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{0915}",
		&["\u{200C}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{00A9}",
		&["\u{200C}", "\u{00A9}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{00A9}",
		&["\u{200C}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0020}",
		&["\u{200C}", "\u{0020}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{0020}",
		&["\u{200C}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0378}",
		&["\u{200C}", "\u{0378}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200C}\u{0308}\u{0378}",
		&["\u{200C}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{000D}",
		&["\u{200D}", "\u{000D}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{000D}",
		&["\u{200D}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{000A}",
		&["\u{200D}", "\u{000A}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{000A}",
		&["\u{200D}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0000}",
		&["\u{200D}", "\u{0000}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{0000}",
		&["\u{200D}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{094D}",
		&["\u{200D}\u{094D}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{094D}",
		&["\u{200D}\u{0308}\u{094D}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0300}",
		&["\u{200D}\u{0300}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{0300}",
		&["\u{200D}\u{0308}\u{0300}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{200C}",
		&["\u{200D}\u{200C}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{200C}",
		&["\u{200D}\u{0308}\u{200C}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{200D}",
		&["\u{200D}\u{200D}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{200D}",
		&["\u{200D}\u{0308}\u{200D}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{1F1E6}",
		&["\u{200D}", "\u{1F1E6}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{1F1E6}",
		&["\u{200D}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{06DD}",
		&["\u{200D}", "\u{06DD}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{06DD}",
		&["\u{200D}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0903}",
		&["\u{200D}\u{0903}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{0903}",
		&["\u{200D}\u{0308}\u{0903}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{1100}",
		&["\u{200D}", "\u{1100}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{1100}",
		&["\u{200D}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{1160}",
		&["\u{200D}", "\u{1160}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{1160}",
		&["\u{200D}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{11A8}",
		&["\u{200D}", "\u{11A8}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{11A8}",
		&["\u{200D}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{AC00}",
		&["\u{200D}", "\u{AC00}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{AC00}",
		&["\u{200D}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{AC01}",
		&["\u{200D}", "\u{AC01}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{AC01}",
		&["\u{200D}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0915}",
		&["\u{200D}", "\u{0915}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{0915}",
		&["\u{200D}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{00A9}",
		&["\u{200D}", "\u{00A9}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{00A9}",
		&["\u{200D}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0020}",
		&["\u{200D}", "\u{0020}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{0020}",
		&["\u{200D}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0378}",
		&["\u{200D}", "\u{0378}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{200D}\u{0308}\u{0378}",
		&["\u{200D}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] ZERO WIDTH JOINER (ZWJ) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{000D}",
		&["\u{1F1E6}", "\u{000D}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{000D}",
		&["\u{1F1E6}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{000A}",
		&["\u{1F1E6}", "\u{000A}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{000A}",
		&["\u{1F1E6}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0000}",
		&["\u{1F1E6}", "\u{0000}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{0000}",
		&["\u{1F1E6}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{094D}",
		&["\u{1F1E6}\u{094D}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{094D}",
		&["\u{1F1E6}\u{0308}\u{094D}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0300}",
		&["\u{1F1E6}\u{0300}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{0300}",
		&["\u{1F1E6}\u{0308}\u{0300}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{200C}",
		&["\u{1F1E6}\u{200C}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{200C}",
		&["\u{1F1E6}\u{0308}\u{200C}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{200D}",
		&["\u{1F1E6}\u{200D}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{200D}",
		&["\u{1F1E6}\u{0308}\u{200D}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{1F1E6}",
		&["\u{1F1E6}\u{1F1E6}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [12.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{1F1E6}",
		&["\u{1F1E6}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{06DD}",
		&["\u{1F1E6}", "\u{06DD}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{06DD}",
		&["\u{1F1E6}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0903}",
		&["\u{1F1E6}\u{0903}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{0903}",
		&["\u{1F1E6}\u{0308}\u{0903}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{1100}",
		&["\u{1F1E6}", "\u{1100}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{1100}",
		&["\u{1F1E6}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{1160}",
		&["\u{1F1E6}", "\u{1160}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{1160}",
		&["\u{1F1E6}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{11A8}",
		&["\u{1F1E6}", "\u{11A8}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{11A8}",
		&["\u{1F1E6}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{AC00}",
		&["\u{1F1E6}", "\u{AC00}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{AC00}",
		&["\u{1F1E6}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{AC01}",
		&["\u{1F1E6}", "\u{AC01}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{AC01}",
		&["\u{1F1E6}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0915}",
		&["\u{1F1E6}", "\u{0915}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{0915}",
		&["\u{1F1E6}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{00A9}",
		&["\u{1F1E6}", "\u{00A9}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{00A9}",
		&["\u{1F1E6}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0020}",
		&["\u{1F1E6}", "\u{0020}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{0020}",
		&["\u{1F1E6}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0378}",
		&["\u{1F1E6}", "\u{0378}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{0308}\u{0378}",
		&["\u{1F1E6}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{000D}",
		&["\u{06DD}", "\u{000D}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{000D}",
		&["\u{06DD}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{000A}",
		&["\u{06DD}", "\u{000A}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{000A}",
		&["\u{06DD}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0000}",
		&["\u{06DD}", "\u{0000}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{0000}",
		&["\u{06DD}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{094D}",
		&["\u{06DD}\u{094D}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{094D}",
		&["\u{06DD}\u{0308}\u{094D}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0300}",
		&["\u{06DD}\u{0300}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{0300}",
		&["\u{06DD}\u{0308}\u{0300}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{200C}",
		&["\u{06DD}\u{200C}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{200C}",
		&["\u{06DD}\u{0308}\u{200C}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{200D}",
		&["\u{06DD}\u{200D}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{200D}",
		&["\u{06DD}\u{0308}\u{200D}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{1F1E6}",
		&["\u{06DD}\u{1F1E6}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{1F1E6}",
		&["\u{06DD}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{06DD}",
		&["\u{06DD}\u{06DD}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{06DD}",
		&["\u{06DD}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0903}",
		&["\u{06DD}\u{0903}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{0903}",
		&["\u{06DD}\u{0308}\u{0903}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{1100}",
		&["\u{06DD}\u{1100}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{1100}",
		&["\u{06DD}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{1160}",
		&["\u{06DD}\u{1160}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{1160}",
		&["\u{06DD}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{11A8}",
		&["\u{06DD}\u{11A8}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{11A8}",
		&["\u{06DD}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{AC00}",
		&["\u{06DD}\u{AC00}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{AC00}",
		&["\u{06DD}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{AC01}",
		&["\u{06DD}\u{AC01}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{AC01}",
		&["\u{06DD}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0915}",
		&["\u{06DD}\u{0915}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{0915}",
		&["\u{06DD}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{00A9}",
		&["\u{06DD}\u{00A9}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{00A9}",
		&["\u{06DD}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0020}",
		&["\u{06DD}\u{0020}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{0020}",
		&["\u{06DD}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0378}",
		&["\u{06DD}\u{0378}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{06DD}\u{0308}\u{0378}",
		&["\u{06DD}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] ARABIC END OF AYAH (Prepend) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{000D}",
		&["\u{0903}", "\u{000D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{000D}",
		&["\u{0903}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{000A}",
		&["\u{0903}", "\u{000A}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{000A}",
		&["\u{0903}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0000}",
		&["\u{0903}", "\u{0000}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{0000}",
		&["\u{0903}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{094D}",
		&["\u{0903}\u{094D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{094D}",
		&["\u{0903}\u{0308}\u{094D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0300}",
		&["\u{0903}\u{0300}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{0300}",
		&["\u{0903}\u{0308}\u{0300}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{200C}",
		&["\u{0903}\u{200C}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{200C}",
		&["\u{0903}\u{0308}\u{200C}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{200D}",
		&["\u{0903}\u{200D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{200D}",
		&["\u{0903}\u{0308}\u{200D}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{1F1E6}",
		&["\u{0903}", "\u{1F1E6}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{1F1E6}",
		&["\u{0903}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{06DD}",
		&["\u{0903}", "\u{06DD}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{06DD}",
		&["\u{0903}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0903}",
		&["\u{0903}\u{0903}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{0903}",
		&["\u{0903}\u{0308}\u{0903}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{1100}",
		&["\u{0903}", "\u{1100}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{1100}",
		&["\u{0903}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{1160}",
		&["\u{0903}", "\u{1160}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{1160}",
		&["\u{0903}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{11A8}",
		&["\u{0903}", "\u{11A8}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{11A8}",
		&["\u{0903}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{AC00}",
		&["\u{0903}", "\u{AC00}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{AC00}",
		&["\u{0903}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{AC01}",
		&["\u{0903}", "\u{AC01}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{AC01}",
		&["\u{0903}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0915}",
		&["\u{0903}", "\u{0915}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{0915}",
		&["\u{0903}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{00A9}",
		&["\u{0903}", "\u{00A9}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{00A9}",
		&["\u{0903}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0020}",
		&["\u{0903}", "\u{0020}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{0020}",
		&["\u{0903}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0378}",
		&["\u{0903}", "\u{0378}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0903}\u{0308}\u{0378}",
		&["\u{0903}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] DEVANAGARI SIGN VISARGA (SpacingMark) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{000D}",
		&["\u{1100}", "\u{000D}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{000D}",
		&["\u{1100}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{000A}",
		&["\u{1100}", "\u{000A}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{000A}",
		&["\u{1100}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0000}",
		&["\u{1100}", "\u{0000}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{0000}",
		&["\u{1100}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{094D}",
		&["\u{1100}\u{094D}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{094D}",
		&["\u{1100}\u{0308}\u{094D}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0300}",
		&["\u{1100}\u{0300}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{0300}",
		&["\u{1100}\u{0308}\u{0300}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{200C}",
		&["\u{1100}\u{200C}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{200C}",
		&["\u{1100}\u{0308}\u{200C}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{200D}",
		&["\u{1100}\u{200D}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{200D}",
		&["\u{1100}\u{0308}\u{200D}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{1F1E6}",
		&["\u{1100}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{1F1E6}",
		&["\u{1100}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{06DD}",
		&["\u{1100}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{06DD}",
		&["\u{1100}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0903}",
		&["\u{1100}\u{0903}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{0903}",
		&["\u{1100}\u{0308}\u{0903}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{1100}",
		&["\u{1100}\u{1100}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [6.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{1100}",
		&["\u{1100}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{1160}",
		&["\u{1100}\u{1160}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [6.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{1160}",
		&["\u{1100}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{11A8}",
		&["\u{1100}", "\u{11A8}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{11A8}",
		&["\u{1100}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{AC00}",
		&["\u{1100}\u{AC00}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [6.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{AC00}",
		&["\u{1100}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{AC01}",
		&["\u{1100}\u{AC01}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [6.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{AC01}",
		&["\u{1100}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0915}",
		&["\u{1100}", "\u{0915}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{0915}",
		&["\u{1100}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{00A9}",
		&["\u{1100}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{00A9}",
		&["\u{1100}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0020}",
		&["\u{1100}", "\u{0020}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{0020}",
		&["\u{1100}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0378}",
		&["\u{1100}", "\u{0378}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{0308}\u{0378}",
		&["\u{1100}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{000D}",
		&["\u{1160}", "\u{000D}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{000D}",
		&["\u{1160}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{000A}",
		&["\u{1160}", "\u{000A}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{000A}",
		&["\u{1160}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0000}",
		&["\u{1160}", "\u{0000}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{0000}",
		&["\u{1160}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{094D}",
		&["\u{1160}\u{094D}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{094D}",
		&["\u{1160}\u{0308}\u{094D}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0300}",
		&["\u{1160}\u{0300}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{0300}",
		&["\u{1160}\u{0308}\u{0300}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{200C}",
		&["\u{1160}\u{200C}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{200C}",
		&["\u{1160}\u{0308}\u{200C}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{200D}",
		&["\u{1160}\u{200D}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{200D}",
		&["\u{1160}\u{0308}\u{200D}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{1F1E6}",
		&["\u{1160}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{1F1E6}",
		&["\u{1160}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{06DD}",
		&["\u{1160}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{06DD}",
		&["\u{1160}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0903}",
		&["\u{1160}\u{0903}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{0903}",
		&["\u{1160}\u{0308}\u{0903}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{1100}",
		&["\u{1160}", "\u{1100}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{1100}",
		&["\u{1160}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{1160}",
		&["\u{1160}\u{1160}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [7.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{1160}",
		&["\u{1160}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{11A8}",
		&["\u{1160}\u{11A8}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [7.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{11A8}",
		&["\u{1160}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{AC00}",
		&["\u{1160}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{AC00}",
		&["\u{1160}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{AC01}",
		&["\u{1160}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{AC01}",
		&["\u{1160}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0915}",
		&["\u{1160}", "\u{0915}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{0915}",
		&["\u{1160}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{00A9}",
		&["\u{1160}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{00A9}",
		&["\u{1160}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0020}",
		&["\u{1160}", "\u{0020}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{0020}",
		&["\u{1160}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0378}",
		&["\u{1160}", "\u{0378}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1160}\u{0308}\u{0378}",
		&["\u{1160}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] HANGUL JUNGSEONG FILLER (V) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{000D}",
		&["\u{11A8}", "\u{000D}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{000D}",
		&["\u{11A8}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{000A}",
		&["\u{11A8}", "\u{000A}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{000A}",
		&["\u{11A8}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0000}",
		&["\u{11A8}", "\u{0000}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{0000}",
		&["\u{11A8}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{094D}",
		&["\u{11A8}\u{094D}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{094D}",
		&["\u{11A8}\u{0308}\u{094D}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0300}",
		&["\u{11A8}\u{0300}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{0300}",
		&["\u{11A8}\u{0308}\u{0300}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{200C}",
		&["\u{11A8}\u{200C}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{200C}",
		&["\u{11A8}\u{0308}\u{200C}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{200D}",
		&["\u{11A8}\u{200D}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{200D}",
		&["\u{11A8}\u{0308}\u{200D}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{1F1E6}",
		&["\u{11A8}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{1F1E6}",
		&["\u{11A8}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{06DD}",
		&["\u{11A8}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{06DD}",
		&["\u{11A8}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0903}",
		&["\u{11A8}\u{0903}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{0903}",
		&["\u{11A8}\u{0308}\u{0903}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{1100}",
		&["\u{11A8}", "\u{1100}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{1100}",
		&["\u{11A8}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{1160}",
		&["\u{11A8}", "\u{1160}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{1160}",
		&["\u{11A8}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{11A8}",
		&["\u{11A8}\u{11A8}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [8.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{11A8}",
		&["\u{11A8}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{AC00}",
		&["\u{11A8}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{AC00}",
		&["\u{11A8}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{AC01}",
		&["\u{11A8}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{AC01}",
		&["\u{11A8}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0915}",
		&["\u{11A8}", "\u{0915}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{0915}",
		&["\u{11A8}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{00A9}",
		&["\u{11A8}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{00A9}",
		&["\u{11A8}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0020}",
		&["\u{11A8}", "\u{0020}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{0020}",
		&["\u{11A8}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0378}",
		&["\u{11A8}", "\u{0378}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{11A8}\u{0308}\u{0378}",
		&["\u{11A8}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] HANGUL JONGSEONG KIYEOK (T) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{000D}",
		&["\u{AC00}", "\u{000D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{000D}",
		&["\u{AC00}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{000A}",
		&["\u{AC00}", "\u{000A}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{000A}",
		&["\u{AC00}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0000}",
		&["\u{AC00}", "\u{0000}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{0000}",
		&["\u{AC00}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{094D}",
		&["\u{AC00}\u{094D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{094D}",
		&["\u{AC00}\u{0308}\u{094D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0300}",
		&["\u{AC00}\u{0300}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{0300}",
		&["\u{AC00}\u{0308}\u{0300}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{200C}",
		&["\u{AC00}\u{200C}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{200C}",
		&["\u{AC00}\u{0308}\u{200C}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{200D}",
		&["\u{AC00}\u{200D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{200D}",
		&["\u{AC00}\u{0308}\u{200D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{1F1E6}",
		&["\u{AC00}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{1F1E6}",
		&["\u{AC00}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{06DD}",
		&["\u{AC00}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{06DD}",
		&["\u{AC00}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0903}",
		&["\u{AC00}\u{0903}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{0903}",
		&["\u{AC00}\u{0308}\u{0903}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{1100}",
		&["\u{AC00}", "\u{1100}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{1100}",
		&["\u{AC00}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{1160}",
		&["\u{AC00}\u{1160}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [7.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{1160}",
		&["\u{AC00}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{11A8}",
		&["\u{AC00}\u{11A8}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [7.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{11A8}",
		&["\u{AC00}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{AC00}",
		&["\u{AC00}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{AC00}",
		&["\u{AC00}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{AC01}",
		&["\u{AC00}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{AC01}",
		&["\u{AC00}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0915}",
		&["\u{AC00}", "\u{0915}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{0915}",
		&["\u{AC00}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{00A9}",
		&["\u{AC00}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{00A9}",
		&["\u{AC00}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0020}",
		&["\u{AC00}", "\u{0020}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{0020}",
		&["\u{AC00}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0378}",
		&["\u{AC00}", "\u{0378}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{0308}\u{0378}",
		&["\u{AC00}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{000D}",
		&["\u{AC01}", "\u{000D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{000D}",
		&["\u{AC01}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{000A}",
		&["\u{AC01}", "\u{000A}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{000A}",
		&["\u{AC01}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0000}",
		&["\u{AC01}", "\u{0000}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{0000}",
		&["\u{AC01}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{094D}",
		&["\u{AC01}\u{094D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{094D}",
		&["\u{AC01}\u{0308}\u{094D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0300}",
		&["\u{AC01}\u{0300}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{0300}",
		&["\u{AC01}\u{0308}\u{0300}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{200C}",
		&["\u{AC01}\u{200C}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{200C}",
		&["\u{AC01}\u{0308}\u{200C}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{200D}",
		&["\u{AC01}\u{200D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{200D}",
		&["\u{AC01}\u{0308}\u{200D}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{1F1E6}",
		&["\u{AC01}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{1F1E6}",
		&["\u{AC01}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{06DD}",
		&["\u{AC01}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{06DD}",
		&["\u{AC01}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0903}",
		&["\u{AC01}\u{0903}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{0903}",
		&["\u{AC01}\u{0308}\u{0903}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{1100}",
		&["\u{AC01}", "\u{1100}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{1100}",
		&["\u{AC01}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{1160}",
		&["\u{AC01}", "\u{1160}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{1160}",
		&["\u{AC01}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{11A8}",
		&["\u{AC01}\u{11A8}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [8.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{11A8}",
		&["\u{AC01}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{AC00}",
		&["\u{AC01}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{AC00}",
		&["\u{AC01}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{AC01}",
		&["\u{AC01}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{AC01}",
		&["\u{AC01}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0915}",
		&["\u{AC01}", "\u{0915}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{0915}",
		&["\u{AC01}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{00A9}",
		&["\u{AC01}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{00A9}",
		&["\u{AC01}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0020}",
		&["\u{AC01}", "\u{0020}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{0020}",
		&["\u{AC01}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0378}",
		&["\u{AC01}", "\u{0378}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{0308}\u{0378}",
		&["\u{AC01}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{000D}",
		&["\u{0915}", "\u{000D}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{000D}",
		&["\u{0915}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{000A}",
		&["\u{0915}", "\u{000A}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{000A}",
		&["\u{0915}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0000}",
		&["\u{0915}", "\u{0000}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{0000}",
		&["\u{0915}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}",
		&["\u{0915}\u{094D}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{094D}",
		&["\u{0915}\u{0308}\u{094D}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0300}",
		&["\u{0915}\u{0300}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{0300}",
		&["\u{0915}\u{0308}\u{0300}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{200C}",
		&["\u{0915}\u{200C}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{200C}",
		&["\u{0915}\u{0308}\u{200C}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{200D}",
		&["\u{0915}\u{200D}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{200D}",
		&["\u{0915}\u{0308}\u{200D}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{1F1E6}",
		&["\u{0915}", "\u{1F1E6}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{1F1E6}",
		&["\u{0915}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{06DD}",
		&["\u{0915}", "\u{06DD}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{06DD}",
		&["\u{0915}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0903}",
		&["\u{0915}\u{0903}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{0903}",
		&["\u{0915}\u{0308}\u{0903}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{1100}",
		&["\u{0915}", "\u{1100}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{1100}",
		&["\u{0915}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{1160}",
		&["\u{0915}", "\u{1160}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{1160}",
		&["\u{0915}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{11A8}",
		&["\u{0915}", "\u{11A8}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{11A8}",
		&["\u{0915}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{AC00}",
		&["\u{0915}", "\u{AC00}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{AC00}",
		&["\u{0915}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{AC01}",
		&["\u{0915}", "\u{AC01}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{AC01}",
		&["\u{0915}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0915}",
		&["\u{0915}", "\u{0915}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{0915}",
		&["\u{0915}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{00A9}",
		&["\u{0915}", "\u{00A9}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{00A9}",
		&["\u{0915}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0020}",
		&["\u{0915}", "\u{0020}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{0020}",
		&["\u{0915}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0378}",
		&["\u{0915}", "\u{0378}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0308}\u{0378}",
		&["\u{0915}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{000D}",
		&["\u{00A9}", "\u{000D}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{000D}",
		&["\u{00A9}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{000A}",
		&["\u{00A9}", "\u{000A}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{000A}",
		&["\u{00A9}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0000}",
		&["\u{00A9}", "\u{0000}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{0000}",
		&["\u{00A9}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{094D}",
		&["\u{00A9}\u{094D}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{094D}",
		&["\u{00A9}\u{0308}\u{094D}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0300}",
		&["\u{00A9}\u{0300}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{0300}",
		&["\u{00A9}\u{0308}\u{0300}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{200C}",
		&["\u{00A9}\u{200C}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{200C}",
		&["\u{00A9}\u{0308}\u{200C}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{200D}",
		&["\u{00A9}\u{200D}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{200D}",
		&["\u{00A9}\u{0308}\u{200D}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{1F1E6}",
		&["\u{00A9}", "\u{1F1E6}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{1F1E6}",
		&["\u{00A9}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{06DD}",
		&["\u{00A9}", "\u{06DD}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{06DD}",
		&["\u{00A9}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0903}",
		&["\u{00A9}\u{0903}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{0903}",
		&["\u{00A9}\u{0308}\u{0903}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{1100}",
		&["\u{00A9}", "\u{1100}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{1100}",
		&["\u{00A9}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{1160}",
		&["\u{00A9}", "\u{1160}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{1160}",
		&["\u{00A9}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{11A8}",
		&["\u{00A9}", "\u{11A8}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{11A8}",
		&["\u{00A9}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{AC00}",
		&["\u{00A9}", "\u{AC00}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{AC00}",
		&["\u{00A9}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{AC01}",
		&["\u{00A9}", "\u{AC01}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{AC01}",
		&["\u{00A9}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0915}",
		&["\u{00A9}", "\u{0915}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{0915}",
		&["\u{00A9}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{00A9}",
		&["\u{00A9}", "\u{00A9}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{00A9}",
		&["\u{00A9}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0020}",
		&["\u{00A9}", "\u{0020}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{0020}",
		&["\u{00A9}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0378}",
		&["\u{00A9}", "\u{0378}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{00A9}\u{0308}\u{0378}",
		&["\u{00A9}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] COPYRIGHT SIGN (ExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{000D}",
		&["\u{0020}", "\u{000D}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{000D}",
		&["\u{0020}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{000A}",
		&["\u{0020}", "\u{000A}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{000A}",
		&["\u{0020}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0000}",
		&["\u{0020}", "\u{0000}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{0000}",
		&["\u{0020}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{094D}",
		&["\u{0020}\u{094D}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{094D}",
		&["\u{0020}\u{0308}\u{094D}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0300}",
		&["\u{0020}\u{0300}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{0300}",
		&["\u{0020}\u{0308}\u{0300}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{200C}",
		&["\u{0020}\u{200C}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{200C}",
		&["\u{0020}\u{0308}\u{200C}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{200D}",
		&["\u{0020}\u{200D}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{200D}",
		&["\u{0020}\u{0308}\u{200D}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{1F1E6}",
		&["\u{0020}", "\u{1F1E6}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{1F1E6}",
		&["\u{0020}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{06DD}",
		&["\u{0020}", "\u{06DD}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{06DD}",
		&["\u{0020}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0903}",
		&["\u{0020}\u{0903}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{0903}",
		&["\u{0020}\u{0308}\u{0903}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{1100}",
		&["\u{0020}", "\u{1100}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{1100}",
		&["\u{0020}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{1160}",
		&["\u{0020}", "\u{1160}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{1160}",
		&["\u{0020}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{11A8}",
		&["\u{0020}", "\u{11A8}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{11A8}",
		&["\u{0020}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{AC00}",
		&["\u{0020}", "\u{AC00}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{AC00}",
		&["\u{0020}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{AC01}",
		&["\u{0020}", "\u{AC01}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{AC01}",
		&["\u{0020}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0915}",
		&["\u{0020}", "\u{0915}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{0915}",
		&["\u{0020}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{00A9}",
		&["\u{0020}", "\u{00A9}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{00A9}",
		&["\u{0020}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0020}",
		&["\u{0020}", "\u{0020}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{0020}",
		&["\u{0020}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0378}",
		&["\u{0020}", "\u{0378}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{0308}\u{0378}",
		&["\u{0020}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{000D}",
		&["\u{0378}", "\u{000D}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{000D}",
		&["\u{0378}\u{0308}", "\u{000D}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <CARRIAGE RETURN (CR)> (CR) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{000A}",
		&["\u{0378}", "\u{000A}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{000A}",
		&["\u{0378}\u{0308}", "\u{000A}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0000}",
		&["\u{0378}", "\u{0000}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{0000}",
		&["\u{0378}\u{0308}", "\u{0000}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [5.0] <NULL> (Control) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{094D}",
		&["\u{0378}\u{094D}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{094D}",
		&["\u{0378}\u{0308}\u{094D}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0300}",
		&["\u{0378}\u{0300}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{0300}",
		&["\u{0378}\u{0308}\u{0300}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING GRAVE ACCENT (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{200C}",
		&["\u{0378}\u{200C}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{200C}",
		&["\u{0378}\u{0308}\u{200C}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH NON-JOINER (ExtendmConjunctLinkermConjunctExtender) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{200D}",
		&["\u{0378}\u{200D}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{200D}",
		&["\u{0378}\u{0308}\u{200D}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{1F1E6}",
		&["\u{0378}", "\u{1F1E6}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{1F1E6}",
		&["\u{0378}\u{0308}", "\u{1F1E6}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{06DD}",
		&["\u{0378}", "\u{06DD}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{06DD}",
		&["\u{0378}\u{0308}", "\u{06DD}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] ARABIC END OF AYAH (Prepend) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0903}",
		&["\u{0378}\u{0903}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{0903}",
		&["\u{0378}\u{0308}\u{0903}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{1100}",
		&["\u{0378}", "\u{1100}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{1100}",
		&["\u{0378}\u{0308}", "\u{1100}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{1160}",
		&["\u{0378}", "\u{1160}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{1160}",
		&["\u{0378}\u{0308}", "\u{1160}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JUNGSEONG FILLER (V) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{11A8}",
		&["\u{0378}", "\u{11A8}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{11A8}",
		&["\u{0378}\u{0308}", "\u{11A8}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL JONGSEONG KIYEOK (T) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{AC00}",
		&["\u{0378}", "\u{AC00}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{AC00}",
		&["\u{0378}\u{0308}", "\u{AC00}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GA (LV) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{AC01}",
		&["\u{0378}", "\u{AC01}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{AC01}",
		&["\u{0378}\u{0308}", "\u{AC01}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] HANGUL SYLLABLE GAG (LVT) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0915}",
		&["\u{0378}", "\u{0915}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{0915}",
		&["\u{0378}\u{0308}", "\u{0915}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{00A9}",
		&["\u{0378}", "\u{00A9}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{00A9}",
		&["\u{0378}\u{0308}", "\u{00A9}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] COPYRIGHT SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0020}",
		&["\u{0378}", "\u{0020}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{0020}",
		&["\u{0378}\u{0308}", "\u{0020}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0378}",
		&["\u{0378}", "\u{0378}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0378}\u{0308}\u{0378}",
		&["\u{0378}\u{0308}", "\u{0378}"],
		"  ÷ [0.2] <reserved-0378> (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] <reserved-0378> (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{000D}\u{000A}\u{0061}\u{000A}\u{0308}",
		&["\u{000D}\u{000A}", "\u{0061}", "\u{000A}", "\u{0308}"],
		"  ÷ [0.2] <CARRIAGE RETURN (CR)> (CR) × [3.0] <LINE FEED (LF)> (LF) ÷ [4.0] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [5.0] <LINE FEED (LF)> (LF) ÷ [4.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{0308}",
		&["\u{0061}\u{0308}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{0020}\u{200D}\u{0646}",
		&["\u{0020}\u{200D}", "\u{0646}"],
		"  ÷ [0.2] SPACE (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] ARABIC LETTER NOON (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0646}\u{200D}\u{0020}",
		&["\u{0646}\u{200D}", "\u{0020}"],
		"  ÷ [0.2] ARABIC LETTER NOON (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] SPACE (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1100}\u{1100}",
		&["\u{1100}\u{1100}"],
		"  ÷ [0.2] HANGUL CHOSEONG KIYEOK (L) × [6.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{AC00}\u{11A8}\u{1100}",
		&["\u{AC00}\u{11A8}", "\u{1100}"],
		"  ÷ [0.2] HANGUL SYLLABLE GA (LV) × [7.0] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{AC01}\u{11A8}\u{1100}",
		&["\u{AC01}\u{11A8}", "\u{1100}"],
		"  ÷ [0.2] HANGUL SYLLABLE GAG (LVT) × [8.0] HANGUL JONGSEONG KIYEOK (T) ÷ [999.0] HANGUL CHOSEONG KIYEOK (L) ÷ [0.3]"
	);
	grapheme_test("\u{1F1E6}\u{1F1E7}\u{1F1E8}\u{0062}",
		&["\u{1F1E6}\u{1F1E7}", "\u{1F1E8}", "\u{0062}"],
		"  ÷ [0.2] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [12.0] REGIONAL INDICATOR SYMBOL LETTER B (RI) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER C (RI) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{1F1E6}\u{1F1E7}\u{1F1E8}\u{0062}",
		&["\u{0061}", "\u{1F1E6}\u{1F1E7}", "\u{1F1E8}", "\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [13.0] REGIONAL INDICATOR SYMBOL LETTER B (RI) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER C (RI) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{1F1E6}\u{1F1E7}\u{200D}\u{1F1E8}\u{0062}",
		&["\u{0061}", "\u{1F1E6}\u{1F1E7}\u{200D}", "\u{1F1E8}", "\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [13.0] REGIONAL INDICATOR SYMBOL LETTER B (RI) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER C (RI) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{1F1E6}\u{200D}\u{1F1E7}\u{1F1E8}\u{0062}",
		&["\u{0061}", "\u{1F1E6}\u{200D}", "\u{1F1E7}\u{1F1E8}", "\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER B (RI) × [13.0] REGIONAL INDICATOR SYMBOL LETTER C (RI) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{1F1E6}\u{1F1E7}\u{1F1E8}\u{1F1E9}\u{0062}",
		&["\u{0061}", "\u{1F1E6}\u{1F1E7}", "\u{1F1E8}\u{1F1E9}", "\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER A (RI) × [13.0] REGIONAL INDICATOR SYMBOL LETTER B (RI) ÷ [999.0] REGIONAL INDICATOR SYMBOL LETTER C (RI) × [13.0] REGIONAL INDICATOR SYMBOL LETTER D (RI) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{200D}",
		&["\u{0061}\u{200D}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{0308}\u{0062}",
		&["\u{0061}\u{0308}", "\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{0903}\u{0062}",
		&["\u{0061}\u{0903}", "\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.1] DEVANAGARI SIGN VISARGA (SpacingMark) ÷ [999.0] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{0600}\u{0062}",
		&["\u{0061}", "\u{0600}\u{0062}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [999.0] ARABIC NUMBER SIGN (Prepend) × [9.2] LATIN SMALL LETTER B (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F476}\u{1F3FF}\u{1F476}",
		&["\u{1F476}\u{1F3FF}", "\u{1F476}"],
		"  ÷ [0.2] BABY (ExtPict) × [9.0] EMOJI MODIFIER FITZPATRICK TYPE-6 (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] BABY (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{1F3FF}\u{1F476}",
		&["\u{0061}\u{1F3FF}", "\u{1F476}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] EMOJI MODIFIER FITZPATRICK TYPE-6 (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] BABY (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{1F3FF}\u{1F476}\u{200D}\u{1F6D1}",
		&["\u{0061}\u{1F3FF}", "\u{1F476}\u{200D}\u{1F6D1}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] EMOJI MODIFIER FITZPATRICK TYPE-6 (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] BABY (ExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) × [11.0] OCTAGONAL SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{1F476}\u{1F3FF}\u{0308}\u{200D}\u{1F476}\u{1F3FF}",
		&["\u{1F476}\u{1F3FF}\u{0308}\u{200D}\u{1F476}\u{1F3FF}"],
		"  ÷ [0.2] BABY (ExtPict) × [9.0] EMOJI MODIFIER FITZPATRICK TYPE-6 (Extend_ConjunctExtendermConjunctLinker) × [9.0] COMBINING DIAERESIS (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) × [11.0] BABY (ExtPict) × [9.0] EMOJI MODIFIER FITZPATRICK TYPE-6 (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1F6D1}\u{200D}\u{1F6D1}",
		&["\u{1F6D1}\u{200D}\u{1F6D1}"],
		"  ÷ [0.2] OCTAGONAL SIGN (ExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) × [11.0] OCTAGONAL SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{200D}\u{1F6D1}",
		&["\u{0061}\u{200D}", "\u{1F6D1}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] OCTAGONAL SIGN (ExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{2701}\u{200D}\u{2701}",
		&["\u{2701}\u{200D}", "\u{2701}"],
		"  ÷ [0.2] UPPER BLADE SCISSORS (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] UPPER BLADE SCISSORS (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{200D}\u{2701}",
		&["\u{0061}\u{200D}", "\u{2701}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] ZERO WIDTH JOINER (ZWJ) ÷ [999.0] UPPER BLADE SCISSORS (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{0924}",
		&["\u{0915}", "\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) ÷ [999.0] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}\u{0924}",
		&["\u{0915}\u{094D}\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}\u{094D}\u{0924}",
		&["\u{0915}\u{094D}\u{094D}\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}\u{200D}\u{0924}",
		&["\u{0915}\u{094D}\u{200D}\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{093C}\u{200D}\u{094D}\u{0924}",
		&["\u{0915}\u{093C}\u{200D}\u{094D}\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN NUKTA (Extend_ConjunctExtendermConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{093C}\u{094D}\u{200D}\u{0924}",
		&["\u{0915}\u{093C}\u{094D}\u{200D}\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN NUKTA (Extend_ConjunctExtendermConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] ZERO WIDTH JOINER (ZWJ) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}\u{0924}\u{094D}\u{092F}",
		&["\u{0915}\u{094D}\u{0924}\u{094D}\u{092F}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] DEVANAGARI LETTER YA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}\u{0061}",
		&["\u{0915}\u{094D}", "\u{0061}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) ÷ [0.3]"
	);
	grapheme_test("\u{0061}\u{094D}\u{0924}",
		&["\u{0061}\u{094D}", "\u{0924}"],
		"  ÷ [0.2] LATIN SMALL LETTER A (XXmLinkingConsonantmExtPict) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{003F}\u{094D}\u{0924}",
		&["\u{003F}\u{094D}", "\u{0924}"],
		"  ÷ [0.2] QUESTION MARK (XXmLinkingConsonantmExtPict) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) ÷ [999.0] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0915}\u{094D}\u{094D}\u{0924}",
		&["\u{0915}\u{094D}\u{094D}\u{0924}"],
		"  ÷ [0.2] DEVANAGARI LETTER KA (LinkingConsonant) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.0] DEVANAGARI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] DEVANAGARI LETTER TA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{0AB8}\u{0AFB}\u{0ACD}\u{0AB8}\u{0AFB}",
		&["\u{0AB8}\u{0AFB}\u{0ACD}\u{0AB8}\u{0AFB}"],
		"  ÷ [0.2] GUJARATI LETTER SA (LinkingConsonant) × [9.0] GUJARATI SIGN SHADDA (Extend_ConjunctExtendermConjunctLinker) × [9.0] GUJARATI SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] GUJARATI LETTER SA (LinkingConsonant) × [9.0] GUJARATI SIGN SHADDA (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1019}\u{1039}\u{1018}\u{102C}\u{1037}",
		&["\u{1019}\u{1039}\u{1018}", "\u{102C}\u{1037}"],
		"  ÷ [0.2] MYANMAR LETTER MA (LinkingConsonant) × [9.0] MYANMAR SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] MYANMAR LETTER BHA (LinkingConsonant) ÷ [999.0] MYANMAR VOWEL SIGN AA (XXmLinkingConsonantmExtPict) × [9.0] MYANMAR SIGN DOT BELOW (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1004}\u{103A}\u{1039}\u{1011}\u{1039}\u{1011}",
		&["\u{1004}\u{103A}\u{1039}\u{1011}\u{1039}\u{1011}"],
		"  ÷ [0.2] MYANMAR LETTER NGA (LinkingConsonant) × [9.0] MYANMAR SIGN ASAT (Extend_ConjunctExtendermConjunctLinker) × [9.0] MYANMAR SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] MYANMAR LETTER THA (LinkingConsonant) × [9.0] MYANMAR SIGN VIRAMA (Extend_ConjunctLinker) × [9.3] MYANMAR LETTER THA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1B12}\u{1B01}\u{1B32}\u{1B44}\u{1B2F}\u{1B32}\u{1B44}\u{1B22}\u{1B44}\u{1B2C}\u{1B32}\u{1B44}\u{1B22}\u{1B38}",
		&["\u{1B12}\u{1B01}", "\u{1B32}\u{1B44}\u{1B2F}", "\u{1B32}\u{1B44}\u{1B22}\u{1B44}\u{1B2C}", "\u{1B32}\u{1B44}\u{1B22}\u{1B38}"],
		"  ÷ [0.2] BALINESE LETTER OKARA TEDUNG (XXmLinkingConsonantmExtPict) × [9.0] BALINESE SIGN ULU CANDRA (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] BALINESE LETTER SA (LinkingConsonant) × [9.0] BALINESE ADEG ADEG (Extend_ConjunctLinker) × [9.3] BALINESE LETTER WA (LinkingConsonant) ÷ [999.0] BALINESE LETTER SA (LinkingConsonant) × [9.0] BALINESE ADEG ADEG (Extend_ConjunctLinker) × [9.3] BALINESE LETTER TA (LinkingConsonant) × [9.0] BALINESE ADEG ADEG (Extend_ConjunctLinker) × [9.3] BALINESE LETTER YA (LinkingConsonant) ÷ [999.0] BALINESE LETTER SA (LinkingConsonant) × [9.0] BALINESE ADEG ADEG (Extend_ConjunctLinker) × [9.3] BALINESE LETTER TA (LinkingConsonant) × [9.0] BALINESE VOWEL SIGN SUKU (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{179F}\u{17D2}\u{178F}\u{17D2}\u{179A}\u{17B8}",
		&["\u{179F}\u{17D2}\u{178F}\u{17D2}\u{179A}\u{17B8}"],
		"  ÷ [0.2] KHMER LETTER SA (LinkingConsonant) × [9.0] KHMER SIGN COENG (Extend_ConjunctLinker) × [9.3] KHMER LETTER TA (LinkingConsonant) × [9.0] KHMER SIGN COENG (Extend_ConjunctLinker) × [9.3] KHMER LETTER RO (LinkingConsonant) × [9.0] KHMER VOWEL SIGN II (Extend_ConjunctExtendermConjunctLinker) ÷ [0.3]"
	);
	grapheme_test("\u{1B26}\u{1B17}\u{1B44}\u{1B13}",
		&["\u{1B26}", "\u{1B17}\u{1B44}\u{1B13}"],
		"  ÷ [0.2] BALINESE LETTER NA (LinkingConsonant) ÷ [999.0] BALINESE LETTER NGA (LinkingConsonant) × [9.0] BALINESE ADEG ADEG (Extend_ConjunctLinker) × [9.3] BALINESE LETTER KA (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{1B27}\u{1B13}\u{1B44}\u{1B0B}\u{1B0B}\u{1B04}",
		&["\u{1B27}", "\u{1B13}\u{1B44}\u{1B0B}", "\u{1B0B}\u{1B04}"],
		"  ÷ [0.2] BALINESE LETTER PA (LinkingConsonant) ÷ [999.0] BALINESE LETTER KA (LinkingConsonant) × [9.0] BALINESE ADEG ADEG (Extend_ConjunctLinker) × [9.3] BALINESE LETTER RA REPA (LinkingConsonant) ÷ [999.0] BALINESE LETTER RA REPA (LinkingConsonant) × [9.1] BALINESE SIGN BISAH (SpacingMark) ÷ [0.3]"
	);
	grapheme_test("\u{1795}\u{17D2}\u{17AF}\u{1798}",
		&["\u{1795}\u{17D2}\u{17AF}", "\u{1798}"],
		"  ÷ [0.2] KHMER LETTER PHA (LinkingConsonant) × [9.0] KHMER SIGN COENG (Extend_ConjunctLinker) × [9.3] KHMER INDEPENDENT VOWEL QE (LinkingConsonant) ÷ [999.0] KHMER LETTER MO (LinkingConsonant) ÷ [0.3]"
	);
	grapheme_test("\u{17A0}\u{17D2}\u{17AB}\u{1791}\u{17D0}\u{1799}",
		&["\u{17A0}\u{17D2}\u{17AB}", "\u{1791}\u{17D0}", "\u{1799}"],
		"  ÷ [0.2] KHMER LETTER HA (LinkingConsonant) × [9.0] KHMER SIGN COENG (Extend_ConjunctLinker) × [9.3] KHMER INDEPENDENT VOWEL RY (LinkingConsonant) ÷ [999.0] KHMER LETTER TO (LinkingConsonant) × [9.0] KHMER SIGN SAMYOK SANNYA (Extend_ConjunctExtendermConjunctLinker) ÷ [999.0] KHMER LETTER YO (LinkingConsonant) ÷ [0.3]"
	);
}
