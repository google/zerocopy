#!/usr/bin/env bash
set -eo pipefail
which yq > /dev/null
jobs=$(for i in $(find .github -iname '*.yaml' -or -iname '*.yml')
  do
    # Select jobs that are triggered by pull request.
    if yq -e '.on | has("pull_request")' "$i" 2>/dev/null >/dev/null
    then
      # This gets the list of jobs that all-jobs-succeed does not depend on.
      comm -23 \
        <(yq -r '.jobs | keys | .[]' "$i" | sort | uniq) \
        <(yq -r '.jobs.all-jobs-succeed.needs[]' "$i" | sort | uniq)
    fi

  # The grep call here excludes all-jobs-succeed from the list of jobs that
  # all-jobs-succeed does not depend on.  If all-jobs-succeed does
  # not depend on itself, we do not care about it.
  done | sort | uniq | (grep -v '^all-jobs-succeed$' || true)
)

if [ -n "$jobs" ]
then
  missing_jobs="$(echo "$jobs" | tr ' ' '\n')"
  echo "all-jobs-succeed missing dependencies on some jobs: $missing_jobs" | tee -a $GITHUB_STEP_SUMMARY
  exit 1
fi
