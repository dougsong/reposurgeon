;; A mode for editing the mailbox-like comment dumps produced by reposurgeon.

(defun decimal-digit-after ()
  (and (>= (char-after) ?0) (<= (char-after) ?9)))

(defun svn-cookify ()
  "Turn a numeric token describing a Subversion reference into a ref cookie."
  (interactive)
  (if (not (decimal-digit-after))
      (error "Expecting decimal digit."))
  (backward-word)
  (if (= (char-after 1) ?r)
      (delete-char 1))
  (insert "[[SVN:")
  (while (decimal-digit-after)
    (forward-char 1))
  (insert "]]")
  )

(defun cvs-rev-char-after ()
  (or (== (char-after) ?.) (decimal-digit-after)))

(defun cvs-cookify ()
  "Turn a token describing a CVS reference into a ref cookie."
  (interactive)
  (if (not (cvs-rev-char-after))
      (error "Expecting decimal digit or dot."))
  (backward-word)
  (insert "[[CVS:")
  (while (cvs-rev-char-after)
    (forward-char 1))
  (insert "]]")
  )

(defvar reposurgeon-mode-map nil "Keymap for reposurgeon-mode")

(when (not reposurgeon-mode-map)
  (setq reposurgeon-mode-map (make-sparse-keymap))
  (define-key reposurgeon-mode-map (kbd "C-x s") 'svn-cookify)
  (define-key reposurgeon-mode-map (kbd "C-x c") 'cvs-cookify)
  )

(define-derived-mode reposurgeon-mode
  text-mode "Reposurgeon"
  "Major mode for editing reposurgeon comment dumps.
\\{reposurgeon-mode-map}"
  (setq case-fold-search nil))

;; end


