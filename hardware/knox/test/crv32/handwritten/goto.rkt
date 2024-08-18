#lang racket/base

(require "test-lib.rkt")

(test-case "goto"
  (check-returns 3 "goto.json"))
