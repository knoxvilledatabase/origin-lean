"""
Compression patterns for Origin extraction.

Each pattern is a class that detects redundant declarations and either
deletes them (returns None) or rewrites them (returns compressed text).

The Extractor calls patterns in order. First match wins.
"""

from .patterns import CompressionPattern, get_patterns
