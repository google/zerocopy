import argparse
import json
import re
import sys
import posixpath

def main():
    parser = argparse.ArgumentParser(description="Validate PR changes against auto-approver rules.")
    parser.add_argument("--config", default=".github/auto-approvers.json", help="Path to the rules JSON.")
    parser.add_argument("--changed-files", default="changed_files.json", help="Path to the fetched changed files JSON.")
    parser.add_argument("--expected-count", type=int, required=True, help="Total number of files expected in the PR.")
    parser.add_argument("--contributors", nargs="+", required=True, help="List of GitHub usernames to validate.")
    args = parser.parse_args()

    # REGEX: Strict path structure, prevents absolute paths and weird characters
    VALID_PATH = re.compile(r'^([a-zA-Z0-9_.-]+/)+$')

    # Load and validate config
    try:
        with open(args.config) as f:
            rules = json.load(f)
    except FileNotFoundError:
        print(f"::error::❌ Config file not found at {args.config}")
        sys.exit(1)

    safe_rules = {}
    for directory, users in rules.items():
        if not isinstance(users, list):
            print(f"::error::❌ Users for '{directory}' must be a JSON array (list), not a string.")
            sys.exit(1)

        if not VALID_PATH.match(directory) or '..' in directory.split('/'):
            print(f"::error::❌ Invalid config path: {directory}")
            sys.exit(1)

        safe_rules[directory] = [str(u).lower() for u in users]

    # Load and flatten changed files
    try:
        with open(args.changed_files) as f:
            file_objects = json.load(f)
    except FileNotFoundError:
        print(f"::error::❌ Changed files JSON not found at {args.changed_files}")
        sys.exit(1)

    if not file_objects or len(file_objects) != args.expected_count:
        print(f"::error::❌ File truncation mismatch or empty PR. Expected {args.expected_count}, got {len(file_objects) if file_objects else 0}.")
        sys.exit(1)

    if not all(isinstance(obj, list) for obj in file_objects):
        print("::error::❌ Invalid payload format. Expected a list of lists.")
        sys.exit(1)

    changed_files = [path for obj in file_objects for path in obj]

    # Validate every file against every contributor
    contributors = set(str(c).lower() for c in args.contributors)
    print(f"👥 Validating contributors: {', '.join(contributors)}")

  for raw_file_path in changed_files:
        file_path = posixpath.normpath(raw_file_path)

        # Find the most specific (longest) matching directory rule.
        longest_match_dir = None
        for directory in safe_rules.keys():
            if file_path.startswith(directory):
                if longest_match_dir is None or len(directory) > len(longest_match_dir):
                    longest_match_dir = directory

        # First, explicitly fail if the file isn't covered by ANY rule.
        if not longest_match_dir:
            print(f"::error::❌ File '{file_path}' does not fall under any configured auto-approve directory.")
            sys.exit(1)

        # Then, verify every contributor has access to that specific rule.
        for user in contributors:
            if user not in safe_rules[longest_match_dir]:
                print(f"::error::❌ Contributor @{user} not authorized for '{file_path}'.")
                sys.exit(1)

    print("✅ Validation passed")

if __name__ == "__main__":
    main()
