#lang racket/base

(require "test-lib.rkt")

(test-case "all builtins"
  (check-returns 27 "builtins.json"))
