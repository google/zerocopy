package org.openelisglobal.common.util;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

// Stub: numeric-value helpers copied verbatim from upstream StringUtil at the pinned commit.
public class StringUtil {
    private static final String DECIMAL_MANTISSA = "[+-]?(?:\\d+\\.?\\d*|\\.\\d+)";
    private static final String SUPERSCRIPT_DIGITS = "⁰¹²³⁴⁵⁶⁷⁸⁹";
    /** Computer scientific notation: 1.5e5, 1.5E+05, -2e-3 */
    private static final Pattern EXPONENT_NOTATION_REG_EX = Pattern
            .compile("^(" + DECIMAL_MANTISSA + ")[eE]([+-]?\\d+)$");
    /**
     * Written scientific notation: 1.5 x 10^5, 1.5×10⁵, 10⁻³ (the mantissa is
     * optional)
     */
    private static final Pattern TIMES_TEN_NOTATION_REG_EX = Pattern.compile("^(?:(" + DECIMAL_MANTISSA
            + ")\\s*[xX×*]\\s*)?([+-]?)10\\s*(?:\\^\\s*([+-]?\\d+)|([⁺⁻]?[" + SUPERSCRIPT_DIGITS + "]+))$");

    public static String getActualNumericValue(String resultValue) {
        String actualValue = resultValue.trim().replaceFirst("^(<=|>=|<|>)", "").trim();
        actualValue = normalizeScientificNotation(actualValue);
        if (isNumeric(actualValue)) {
            return actualValue;
        } else {
            return "NaN";
        }
    }

    public static String normalizeScientificNotation(String value) {
        if (value == null || value.trim().isEmpty()) {
            return value;
        }
        String candidate = value.trim();
        Matcher exponent = EXPONENT_NOTATION_REG_EX.matcher(candidate);
        if (exponent.matches()) {
            return canonicalExponentNotation(exponent.group(1), exponent.group(2), value);
        }
        Matcher timesTen = TIMES_TEN_NOTATION_REG_EX.matcher(candidate);
        if (timesTen.matches()) {
            String mantissa = timesTen.group(1) != null ? timesTen.group(1) : timesTen.group(2) + "1";
            String power = timesTen.group(3) != null ? timesTen.group(3) : superscriptToAscii(timesTen.group(4));
            return canonicalExponentNotation(mantissa, power, value);
        }
        return value;
    }

    private static String canonicalExponentNotation(String mantissa, String power, String original) {
        try {
            int exponent = Integer.parseInt(power.startsWith("+") ? power.substring(1) : power);
            return (mantissa.startsWith("+") ? mantissa.substring(1) : mantissa) + "e" + exponent;
        } catch (NumberFormatException e) {
            return original;
        }
    }

    private static String superscriptToAscii(String superscripts) {
        StringBuilder ascii = new StringBuilder(superscripts.length());
        for (int i = 0; i < superscripts.length(); i++) {
            char c = superscripts.charAt(i);
            int digit = SUPERSCRIPT_DIGITS.indexOf(c);
            if (digit >= 0) {
                ascii.append(digit);
            } else if (c == '⁺') {
                ascii.append('+');
            } else if (c == '⁻') {
                ascii.append('-');
            }
        }
        return ascii.toString();
    }

    public static boolean isNumeric(String str) {
        if (str == null)
            return false;
        try {
            double parsed = Double.parseDouble(normalizeScientificNotation(str));
            return !Double.isNaN(parsed) && !Double.isInfinite(parsed);
        } catch (NumberFormatException e) {
            return false;
        }
    }
}
