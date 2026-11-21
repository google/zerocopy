"""Minimal import shims so that the unmodified upstream PySlope analysis core can
be imported without its plotting/progress-bar dependencies (plotly, tqdm,
colour). Only the numerical analysis paths are exercised; plotting is not.
Usage: import pyslope_shims  (before importing pyslope)."""
import sys, types

# tqdm: identity iterator
tq = types.ModuleType("tqdm")
tq.tqdm = lambda it, *a, **k: it
sys.modules["tqdm"] = tq

# plotly.graph_objects: attribute access returns a no-op callable
class _NoOp:
    def __getattr__(self, name):
        return _NoOp()
    def __call__(self, *a, **k):
        return _NoOp()
plotly = types.ModuleType("plotly")
go = types.ModuleType("plotly.graph_objects")
go.__getattr__ = lambda name: _NoOp()
plotly.graph_objects = go
sys.modules["plotly"] = plotly
sys.modules["plotly.graph_objects"] = go

# colour.Color: utilities.py builds colour gradients at import time
col = types.ModuleType("colour")
class Color:
    def __init__(self, c=None, *a, **k):
        self.c = c
    def range_to(self, other, n):
        return [Color(self.c) for _ in range(int(n))]
    @property
    def hex(self):
        return "#000000"
    @property
    def hex_l(self):
        return "#000000"
    def get_hex(self):
        return "#000000"
    def get_hex_l(self):
        return "#000000"
    def __str__(self):
        return "#000000"
col.Color = Color
sys.modules["colour"] = col
