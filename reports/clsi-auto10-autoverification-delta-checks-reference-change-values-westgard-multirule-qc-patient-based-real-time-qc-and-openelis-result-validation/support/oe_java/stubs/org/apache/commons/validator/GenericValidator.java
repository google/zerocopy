package org.apache.commons.validator;
// Stub reproducing commons-validator semantics for the two methods used.
public class GenericValidator {
    public static boolean isBlankOrNull(String value) { return value == null || value.trim().length() == 0; }
    public static boolean isDouble(String value) {
        if (value == null) return false;
        try { Double.parseDouble(value); return true; } catch (NumberFormatException e) { return false; }
    }
}
