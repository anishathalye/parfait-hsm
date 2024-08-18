#lang racket/base

(require "test-lib.rkt")

(test-case "misc instructions"
  (check-returns 0 "misc.json"))
