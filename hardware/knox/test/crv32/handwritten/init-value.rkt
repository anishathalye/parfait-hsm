#lang racket/base

(require "test-lib.rkt")

(test-case "initializing global variables"
  (check-returns 26 "init_value.json"))
