;; A mode for editing the mailbox-like comment dumps produced by reposurgeon.
;;
;; Canonicalizing thousands of comments in a mailbox_out dump is the grottiest
;; part of lifting a repository, but if you don't do it you are probably going
;; to miss things that should turn into reference cookies.  This mode aims to
;; speed up the process.
;;
;; Work in progress - neither code nor bindings should be considered stable.

(defconst svn-log-delimiter
  "------------------------------------------------------------------------\n"
  "Delimiter line used in the output of svn log")

(defconst reposurgeon-mail-delimiter
  "------------------------------------------------------------------------------\n"
  "Delimiter line used in reposurgeon comment mailboxes.")

(defun decimal-digit-after ()
  (and (>= (char-after) ?0) (<= (char-after) ?9)))

(defun svn-cookify ()
  "Turn a Subversion revision number around point into a reference cookie."
  (interactive)
  (if (not (decimal-digit-after))
      (error "Expecting decimal digit."))
  (backward-word)
  ;; Ignore preceding r
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
  "Turn CVS reference around point into a reference cookie."
  (interactive)
  (if (not (cvs-rev-char-after))
      (error "Expecting decimal digit or dot."))
  (backward-word)
  (insert "[[CVS:")
  (while (cvs-rev-char-after)
    (forward-char 1))
  (insert "]]")
  )

(defun gitify-comment ()
  "Break the first line of a paragraph comment following git conventions."
  (interactive)
  (delete-horizontal-space)
  (if (= (char-after) ?\n) (delete-char 1))
  (let ((c (char-before)))
	(cond ((member c '(?\. ?\! ?\?))
	       (insert "\n\n"))
	      ((member c '(?\, ?\: [semicolon] ?\,))
	       (insert "\n\n..."))
	      (t
	       (insert "...\n\n...")))))

(defun svn-reference-lift ()
  "Interactively lift probable SVN revision numbers into ref cookies en masse."
  (interactive)
  (query-replace-regexp "\\br\\([0-9][0-9]+\\)\\b" "[[SVN:\\1]]"))

(defun svn-lift-log ()
  "After pasting a segment of a Subversion log dump, this will fix delimiters
and headers so it's in the same format as the rest of the mailbox."
  (interactive)
  (while (re-search-forward (concat svn-log-delimiter "r\\([0-9]+\\).*") nil t)
    (replace-match (concat reposurgeon-mail-delimiter "Fossil-ID: \\1") nil nil)))

(defun bzr-reference-lift ()
  "Interactively lift probable Bazaar revision numbers into ref cookies en masse."
  (interactive)
  (query-replace-regexp "\\brevision \\([0-9][0-9.]+\\)\\b" "[[BZR:\\1]]"))

(defun clean-until-committer ()
  "Remove all headers from next mbox entry until Committer and Committer-Date."
  (interactive)
  (re-search-forward (concat "^" reposurgeon-mail-delimiter))
  (let ((kill-whole-line t))
    (while (not (looking-at "^Committer:\\|^$"))
      (kill-line)))
  )

(defun kill-comment-entry ()
  "Remove current mailbox entry, move to next."
  (interactive)
  (re-search-backward (concat "^" reposurgeon-mail-delimiter))
  (beginning-of-line)
  (forward-line 1)
  (let ((kill-whole-line t))
    (while (not (looking-at (concat "^" reposurgeon-mail-delimiter)))
      (kill-line))
    (kill-line))
  )

(defvar reposurgeon-mode-map nil "Keymap for reposurgeon-mode")

(when (not reposurgeon-mode-map)
  (setq reposurgeon-mode-map (make-sparse-keymap))
  (define-key reposurgeon-mode-map (kbd "C-x s") 'svn-cookify)
  (define-key reposurgeon-mode-map (kbd "C-x c") 'cvs-cookify)
  (define-key reposurgeon-mode-map (kbd "C-x .") 'gitify-comment)
  (define-key reposurgeon-mode-map (kbd "C-x C-k") 'kill-comment-entry)
  )

(define-derived-mode reposurgeon-mode
  text-mode "Reposurgeon"
  "Major mode for editing reposurgeon comment mailboxes.
\\{reposurgeon-mode-map}"
  (setq case-fold-search nil))

;; end


