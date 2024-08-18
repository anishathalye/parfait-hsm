#lang racket/base

(require "test-lib.rkt")

(test-case "div/rem"
  (check-returns 0 "divrem.json"))
