"""Diagnostic text-preservation check; not a replacement for strict Carcara."""
import argparse
import json
from pathlib import Path
import re


def verify(original, translated):
    before, after = original.splitlines(), translated.splitlines()
    def conclusions(lines):
        result = {}
        for line in lines:
            match = re.match(r'\(step (\S+) (.*) :rule ', line)
            if match:
                if match[1] in result:
                    raise ValueError('duplicate textual step identifier')
                result[match[1]] = match[2]
        return result
    old_steps, new_steps = conclusions(before), conclusions(after)
    if any(new_steps.get(name) != conclusion for name, conclusion in old_steps.items()):
        raise ValueError('original step conclusion changed or omitted')
    if ([line for line in before if line.startswith('(assume ')] !=
            [line for line in after if line.startswith('(assume ')]):
        raise ValueError('assumption changed or added')
    cursor = 0
    for line in before:
        if ':rule rare_rewrite' in line:
            continue
        try:
            cursor = after.index(line, cursor) + 1
        except ValueError:
            raise ValueError('non-rewrite proof line removed or reordered') from None
    return {'all_original_step_conclusions_byte_identical': True,
            'all_assumption_lines_byte_identical': True,
            'nonrewrite_lines_preserved_in_order': True,
            'original_steps': len(old_steps), 'translated_steps': len(new_steps)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original', type=Path, required=True)
    parser.add_argument('--translated', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.original.read_text(), args.translated.read_text()), indent=2))


if __name__ == '__main__':
    main()
