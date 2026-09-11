import { combineReducers } from '@reduxjs/toolkit';

import assembly from './assembly';
import clippy from './clippy';
import execute from './execute';
import format from './format';
import gist from './gist';
import hir from './hir';
import llvmIr from './llvmIr';
import macroExpansion from './macroExpansion';
import meta from './meta';
import mir from './mir';
import miri from './miri';
import wasm from './wasm';

const output = combineReducers({
  meta,
  format,
  clippy,
  miri,
  macroExpansion,
  assembly,
  llvmIr,
  mir,
  hir,
  wasm,
  execute,
  gist,
});

export default output;
