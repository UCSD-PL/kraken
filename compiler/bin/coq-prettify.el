(defun coq-prettify ()
   "Format entire Coq buffer."
   (coq-indent-region (point-min) (point-max))
   (untabify (point-min) (point-max))
   (save-buffer)
   (kill-emacs)
)
