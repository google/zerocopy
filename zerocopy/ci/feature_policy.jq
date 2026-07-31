# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Derive the semantic feature sets which ci.yml must exercise. Keep this file
# coordinated with check_all_toolchains_tested.sh, which supplies the manifest
# data and consumes every field below, and test_feature_policy.sh, which
# exercises dependency-edge cases without rewriting Cargo.toml.
#
# Cargo features can affect a build in three distinct ways:
#
# - a local feature name enables another local feature;
# - `dep:foo` activates an optional dependency; and
# - `foo/bar` or `foo?/bar` enables a feature of a dependency (with only the
#   non-weak spelling also activating an optional `foo` dependency).
#
# Tracking only the first category is insufficient. In particular, a future
# `default = ["dep:foo"]` must both require a no-default matrix cell and be
# rejected unless the stable profile activates the same dependency. Model the
# other two categories as `effect:` nodes in the closure. They are retained for
# subset comparisons but filtered out when comparing local feature names.

def feature_node($feature): "feature:\($feature)";
def effect_node($effect): "effect:\($effect)";

def edge_nodes($graph; $optional_dependencies; $seen; $edges):
  $edges[]
  | . as $edge
  | if ($graph | has($edge))
    then feature_node($edge)
    elif ($edge | startswith("dep:"))
    then effect_node($edge)
    elif ($edge | test("^[^?/]+/"))
    then ($edge | split("/")[0]) as $dependency
      # A non-weak dependency-feature edge activates an optional dependency.
      # Cargo also enables the dependency's same-named local feature when that
      # node exists, including any local edges reachable through it. Record all
      # three so stable-vs-default comparison covers both the crate's cfgs and
      # the complete dependency configuration.
      | if ($optional_dependencies | index($dependency)) != null
        then
          (if ($graph | has($dependency))
           then feature_node($dependency)
           else empty
           end),
          effect_node("dep:\($dependency)"),
          effect_node($edge)
        else effect_node($edge)
        end
    elif ($edge | test("^[^/]+\\?/"))
    then ($edge | split("?/")[0]) as $dependency
      # Weak forwarding configures `foo` only if another edge has already
      # activated it. Because closure revisits local feature nodes until a
      # fixed point, an activation discovered later will make this edge take
      # effect on the following iteration. Canonicalize the resulting effect
      # to `foo/bar`: once active, weak and non-weak forwarding configure the
      # dependency identically.
      | select($seen | index(effect_node("dep:\($dependency)")) != null)
      | effect_node($edge | sub("\\?/"; "/"))
    # Cargo metadata should not contain any other edge form. Retaining an
    # unknown edge as an effect is deliberately fail-closed: if a new Cargo
    # syntax reaches a default feature, the stable profile must reach the same
    # edge until this policy is taught its exact semantics.
    else effect_node($edge)
    end;

def closure($graph; $optional_dependencies; $seed):
  def visit($seen):
    ([
      $seen[]
      | select(startswith("feature:"))
      | ltrimstr("feature:") as $feature
      | edge_nodes(
          $graph;
          $optional_dependencies;
          $seen;
          ($graph[$feature] // [])
        )
    ] | unique) as $next
    | (($seen + $next) | unique) as $new
    | if ($new | length) == ($seen | length)
      then $new
      else visit($new)
      end;
  visit($seed | unique);

. as $input
| $input.graph as $graph
| $input.optional_dependencies as $optional_dependencies
| $input.nightly as $nightly
| $input.stable_feature as $stable_feature
| ($graph | keys) as $keys
| ($graph.default // []) as $default_direct
| closure(
    $graph;
    $optional_dependencies;
    [feature_node($stable_feature)]
  ) as $stable_nodes
| (if ($graph | has("default"))
   then closure(
     $graph;
     $optional_dependencies;
     [feature_node("default")]
   ) - [feature_node("default")]
   else []
   end) as $default_nodes
| {
    stable_feature_exists: ($graph | has($stable_feature)),
    nightly_unknown: ($nightly - $keys | unique),
    nightly_default_entry: ($nightly | index("default") != null),
    stable_actual: [
      $stable_nodes[]
      | select(startswith("feature:"))
      | ltrimstr("feature:")
    ],
    stable_expected: ($keys - ["default"] - $nightly | unique),
    default_direct: $default_direct,
    # Enabling even an empty `default` feature emits cfg(feature = "default").
    # Its mere presence therefore requires a no-default profile; the closure
    # below separately describes what else the feature enables.
    default_feature_exists: ($graph | has("default")),
    default_closure: [
      $default_nodes[]
      | sub("^(feature|effect):"; "")
    ],
    default_outside_stable: [
      ($default_nodes - $stable_nodes)[]
      | sub("^(feature|effect):"; "")
    ],
    default_nightly: [
      $default_nodes[]
      | select(startswith("feature:"))
      | ltrimstr("feature:")
      | select($nightly | index(.) != null)
    ],
    std_feature_exists: ($keys | index("std") != null),
    stable_enables_std: ($stable_nodes | index(feature_node("std")) != null),
    default_enables_std: ($default_nodes | index(feature_node("std")) != null)
  }
