;;;; -*- Mode: Lisp; Syntax: Common-Lisp -*-
;;;; Code from Paradigms of AI Programming
;;;; Copyright (c) 1991 Peter Norvig
;;;; Modified by Giridhar Murali

;;;; File sudoku.lisp: Sudoku Creation and Solving
;;;; Original File waltz.lisp: Constraint Propagation for line labeling problem

;;------------------------------------------------------------------------------
;; Basic Data Structures and Variables
;;------------------------------------------------------------------------------


(defstruct (puzzle (:print-function show-puzzle))
  "A puzzle is a list of coordinates." coordinates)

(defstruct coordinate
  "A coordinate is the smallest building block of a puzzle"
  (name nil :type atom)                                                                  ;; Name of coordinate to uniquely identify it (1 to d)
  (x nil :type atom)                                                                     ;; X position of coordinate
  (y nil :type atom)                                                                     ;; Y position of coordinate
  (grid nil :type atom)                                                                  ;; Grid to which the coordinate belongs to (1 to a)
  (neighbors nil :type list)                                                             ;; of coordinates (in the same row, colomn and grid, except itself)
  (labelings nil :type list))                                                            ;; of values from (member (list 1-d))

(defvar *aritysq* 9)                                                                     ;; Square of arity. 
                                                                                         ;; Adjusted because of initial misunderstanding of the term
(defvar *select-variable*)                                                               ;; Variable Selection Function. 
(defvar *guesses* 0)                                                                     ;; Keeps track of number of guesses made for coordinate values


;;------------------------------------------------------------------------------
;; Top Level Functions
;;------------------------------------------------------------------------------

(defun create-puzzle (arity-input &optional coordinate-descriptors)
  "Build a new puzzle from the given arity and coordinate-descriptor tuples."
  (if (and (integerp arity-input) (> arity-input 1))
  (let ((puzzle (make-puzzle)))    
    (setf *aritysq* (* arity-input arity-input))
    (setf (puzzle-coordinates puzzle)
      (mapcar #'construct-coordinate 
        (possible-labelings 1 (* *aritysq* *aritysq*))))                                 ;; Create a list of coordinates with names initialized
    (dolist (coordname (puzzle-coordinates puzzle))                                      ;; Initialize x,y,grid & labelings values
       (populate-descriptors coordname)
      (setf (coordinate-labelings coordname) (possible-labelings 1 *aritysq*)))
    (dolist (coordname (puzzle-coordinates puzzle))
          (populate-neighbors coordname puzzle))                                         ;; Populate neighbors for all coordinates
    (if (all-valid-values coordinate-descriptors)
        (modify-puzzle puzzle coordinate-descriptors)                                    ;; Add in values from the initialization tuples
     (error "Invalid tuples"))
    (if (validate-puzzle puzzle)                                                         ;; Check if the created puzzle follows all rules of sudoku
        (progn (format t "Puzzle Created")
          (show-puzzle puzzle)                                                           ;; Display the puzzle
          puzzle) (error "Puzzle Creation Failed")))
  (error "Invalid Arity. Arity must be greater than 1 to create a sensible puzzle.")))
  

(defun create-unambiguous-puzzle (puzzle)
  "Fill in entries just enough for the puzzle to have one unique solution"
  (show-puzzle puzzle "~&The initial puzzle is:")
  (if (solvable-puzzle-p puzzle)
      (progn
        (format t "This is an unambiguous puzzle:")
        (show-puzzle puzzle)
        )
  (progn 
  (every #'propagate-constraints (puzzle-coordinates puzzle))
  (if (impossible-puzzle-p puzzle)
       (format t "Impossible Puzzle")
    (search-unambiguous-puzzle puzzle)))))

(defun print-solutions (puzzle)
  "Label the puzzle by propagating constraints and then
  searching for solutions if necessary.  Print all solutions."
  (show-puzzle puzzle "~&The initial puzzle is:")
  (every #'propagate-constraints (puzzle-coordinates puzzle))
  (show-puzzle puzzle
                "~2&After constraint propagation the puzzle is:")
  (let* ((solutions (if (impossible-puzzle-p puzzle)
                        nil
                        (search-solutions puzzle)))
         (n (length solutions)))
    (if (= n 1)
        (show-puzzle (first solutions)))
    (unless (= n 1)
      (format t "~2&There are ~r solution~:p:" n)
      (mapc #'show-puzzle solutions)))
  (values))

(defun print-solution (puzzle &key (vsf 'first-ambiguous))
  "Label the puzzle by propagating constraints and then
  searching for solutions if necessary.  Print first solution."
  (setf *guesses* 0)
  (setf (symbol-function 'first-ambiguous) #'first-ambiguous)
  (setf (symbol-function 'random-ambiguous) #'random-ambiguous)
  (setf (symbol-function 'mrv-ambiguous) #'mrv-ambiguous)
  (setf *select-variable* vsf)
  (show-puzzle puzzle "~&The initial puzzle is:")
  (every #'propagate-constraints (puzzle-coordinates puzzle))
  (show-puzzle puzzle
               "~2&After constraint propagation the puzzle is:")
  (if (impossible-puzzle-p puzzle)
       (format t "Impossible Puzzle")
    (print-unambiguous-puzzle puzzle)))

;;--------------------------------------------------------------------------------
;; Functions to check coordinate types
;;--------------------------------------------------------------------------------

(defun ambiguous-coordinate-p (coordinate)
  "A coordinate is ambiguous if it has more than one labeling."
  (> (number-of-labelings coordinate) 1))

(defun fixed-coordinate-p (coordinate)
  "A coordinate is fixed if it has exactly one labeling."
  (= 1 (number-of-labelings coordinate)))

(defun impossible-coordinate-p (coordinate)
  "A coordinate is impossible if it has no labeling."
  (null (coordinate-labelings coordinate)))

;;-----------------------------------------------------------------------------------
;; Functions to check puzzle types
;;-----------------------------------------------------------------------------------

(defun impossible-puzzle-p (puzzle)
  "An impossible puzzle is one with an impossible coordinate."
  (some #'impossible-coordinate-p (puzzle-coordinates puzzle)))

(defun solvable-puzzle-p (puzzle)
  "A solvable puzzle is one with a unique solution"
  (setf puzzle2 (make-copy-puzzle puzzle))
  (every #'propagate-constraints (puzzle-coordinates puzzle2))
  (if (impossible-puzzle-p puzzle2)
      nil
    (progn
      (setf solutions (search-solutions puzzle2))
      (if (and (= 1 (length solutions)) (validate-puzzle (first solutions)))
          t))))

;;-----------------------------------------------------------------------------------
;; Functions that operate on labelings
;;-----------------------------------------------------------------------------------

(defun number-of-labelings (coordinate)
  "Returns number of labelings bounded to a coordinate"
  (length (coordinate-labelings coordinate)))

(defun possible-labelings (ini fin)
  "Initially, possible labelings is a list of numbers from 1 to fin."
    (if (> ini fin)
            (if (eql ini fin)
            (cons fin nil)
            (cons ini (possible-labelings (- ini 1) fin)))
        
            (if (eql ini fin)
            (cons fin nil)
              (cons ini (possible-labelings (+ ini 1) fin)))))

(defun consistent-labelings (coordinate)
  (setf fixed-neighbors (coordinate-neighbors coordinate))
  (setf fixed-neighbors (remove-if #'ambiguous-coordinate-p fixed-neighbors))                ;; List of neighbors that have a value fixed
  (if (> (length fixed-neighbors) 0)                                                         ;; Operate only of the co-ordinate has any fixed-neighbors
      (operate-on-labelings fixed-neighbors coordinate)
      (coordinate-labelings coordinate)))                                                    ;; Otherwise return the same old labelings

(defun operate-on-labelings (fixed-neighbors coordinate)
 (setf labelings (list nil))
 (dolist (neighbor fixed-neighbors)                                                          ;; In the list of fixed-neighbors
 (setf labelings (cons (first (coordinate-labelings neighbor)) labelings)))                  ;; Make a list of all labelings 
 (setf labelings (remove-duplicates (delete nil labelings)))                                 ;; Remove initialization 'nil'
 (update-labelings coordinate labelings)                                                     ;; Update labelings with consistent labels alone
  )

(defun update-labelings (coordinate labelings)
  "Remove common labels between labelings and coordinate-labelings" 
  (setf ixn (intersection (coordinate-labelings coordinate) labelings))                      ;; Find the common elements
  (dolist (label ixn)
    (setf (coordinate-labelings coordinate)
      (delete label (coordinate-labelings coordinate)))                                      ;; Delete common elements and update labelings
    )(coordinate-labelings coordinate))


;;-----------------------------------------------------------------------------------
;; Variable Selection Functions
;;-----------------------------------------------------------------------------------


(defun first-ambiguous (puzzle)
  (find-if #'ambiguous-coordinate-p
                    (puzzle-coordinates puzzle)))

(defun random-ambiguous (puzzle)
  (random-elt (remove-if-not #'ambiguous-coordinate-p
                             (puzzle-coordinates puzzle))))

(defun mrv-ambiguous (puzzle) 
  (if (= 0 (length (remove-if-not #'ambiguous-coordinate-p (puzzle-coordinates puzzle))))
      nil
    (first (sort (remove-if-not #'ambiguous-coordinate-p (puzzle-coordinates puzzle))
                 #'< :key #'number-of-labelings)))
)

;;---------------------------------------------------------------------------------------
;; Supporting functions for creating puzzle
;;---------------------------------------------------------------------------------------

(defun populate-descriptors (coordname)
  "Build a list of x,y and grid value for the given coordname"
  (setf coord (coordinate-name coordname))
  (setf qr (multiple-value-list (floor coord *aritysq*)))                                     ;; qr is a list with quotient and remainder
  (cond ((eql (second qr) 0)
           (setf (coordinate-x coordname) *aritysq*)
           (setf (coordinate-y coordname) (first qr)))
       (t  (setf (coordinate-x coordname) (second qr))
           (setf (coordinate-y coordname) (+ (first qr) 1)))
        )
  (setf grid-size (isqrt *aritysq*))
  (setf qr1 (multiple-value-list (floor (coordinate-x coordname) grid-size)))
  (setf qr2 (multiple-value-list (floor (coordinate-y coordname) grid-size)))
  (cond ((eql (second qr1) 0)
         (setf t1 (first qr1)))
         (t
            (setf t1 (+ (first qr1) 1)))
        )
  (cond ((eql (second qr2) 0)
         (setf t2 (first qr2)))
         (t
            (setf t2 (+ (first qr2) 1)))
        )
  (setf (coordinate-grid coordname) (+ t1 (* grid-size (- t2 1))))
)

(defun populate-neighbors (coordname puzzle)
  "Set list of neighbors for all coordinates in the puzzle"
  ;; In the list of coords, check if x,y or grid is same
  ;; If same, add to list of neighbors
  ;; Finally, delete all occurrences of coordname from the list
  (setf neighbors-list (list nil))                                           
  (dolist (neighbor (puzzle-coordinates puzzle))                                               ;; For each co-ordinate
    (if (or (= (coordinate-x neighbor) (coordinate-x coordname))                               ;; When x, y or grid is the same value
              (= (coordinate-y neighbor) (coordinate-y coordname))
              (= (coordinate-grid neighbor) (coordinate-grid coordname))
            )(setf neighbors-list (cons neighbor neighbors-list)))                             ;; Add coordinate to list of neighbors  
    )
  (setf neighbors-list (delete nil neighbors-list))                                            ;; Delete "nil" from the list of neighbors 
  (setf neighbors-list (delete coordname neighbors-list))                                      ;; Delete the coordinate from the list of its neighbors
  (setf neighbors-list (delete-duplicates neighbors-list))                                     ;; Delete all duplicates 
  (setf (coordinate-neighbors coordname) neighbors-list)                                       ;; Finally, assign this list to the neighbors parameter
 )

(defun all-valid-values (tuples)
  (if (every #'valid-value-p (apply #'append tuples))                                          ;; Check if each one of them is valid  
      t
    ))
     
(defun modify-puzzle (puzzle tuples)
  "Modify the puzzle to set values for coordinates from the initialization tuples"  
  (dolist (values tuples)  
    (setf coord (+ (second values) (* *aritysq* (- (first values) 1))))                        ;; Get coordinate-name from x and y values
    (setf coordinate (find-coordinate coord puzzle))                                           ;; Find coordinate with the calculated coordinate-name
    (if (ambiguous-coordinate-p coordinate)                                                    ;; Set value only if particular coordinate is not already set
        (setf (coordinate-labelings coordinate) (list (third values)))
      (error "~% Coordinate already has a binding. Ignoring Tuple.. ~%"))
    ))

(defun construct-coordinate (coordname) 
  "Build the coordinate corresponding to the coordinate name passed."
   (make-coordinate
    :name coordname
    ))

(defun validate-puzzle (puzzle)
  (dolist (coord (puzzle-coordinates puzzle))
    (if (fixed-coordinate-p coord)
    (dolist (neighbor (coordinate-neighbors coord))
      (if (fixed-coordinate-p neighbor)
          (if (= (first (coordinate-labelings coord)) (first (coordinate-labelings neighbor)))
              (error "Invalid Puzzle Tuples")
            t) t)) t)) t)

;;-------------------------------------------------------------------------------------
;; Constraint Propagation Functions
;;-------------------------------------------------------------------------------------

(defun propagate-constraints (coordinate)
  "Reduce the labelings on coordinate by considering neighbors.
  If we can reduce, propagate the constraints to each neighbor."
  ;; Return nil only when the constraints lead to an impossibility
    (let ((old-num (number-of-labelings coordinate)))
    (setf (coordinate-labelings coordinate) (consistent-labelings coordinate))
    (unless (impossible-coordinate-p coordinate)
      (when (< (number-of-labelings coordinate) old-num)
        (every #'propagate-constraints (coordinate-neighbors coordinate)))
      t)))

(defun search-solutions (puzzle)
  "Try all labelings for one ambiguous coordinate, and propagate."
   (let ((v (funcall #'first-ambiguous puzzle)))
    (if (null v)
        (list puzzle)
        (mapcan 
          #'(lambda (v-labeling)
              (let* ((puzzle2 (make-copy-puzzle puzzle))
                     (v2 (find-coordinate (coordinate-name v) puzzle2)))
                (setf (coordinate-labelings v2) (list v-labeling))                           
                (if (propagate-constraints v2)
                    (search-solutions puzzle2)
                    nil)))
          (coordinate-labelings v)))))  

(defun print-unambiguous-puzzle (puzzle)
  "Try all labelings for one ambiguous coordinate, and propagate."
  (if (solvable-puzzle-p puzzle)
      (progn
        (format t "The solution is:")
        (show-puzzle (first (search-solutions puzzle)))
        (format t "~%Solved with ~a guesses." *guesses*)
          )
       (let* ((v (funcall *select-variable* puzzle)))
         (if (null v)
             (progn
               (format t "~% No more ambiguous coordinates. The solution is:")
               (show-puzzle puzzle)
               (format t "~%Solved with ~a guesses." *guesses*))
       (let* ((puzzle2 (make-copy-puzzle puzzle))
              (v2 (find-coordinate (coordinate-name v) puzzle2)))
         (setf v-labeling (random-elt (coordinate-labelings v)))
         (format t "~% Choosing ~a for coordinate ~a" v-labeling (coordinate-name v2)) 
         (setf *guesses* (+ 1 *guesses*))
         (setf (coordinate-labelings v2) (list v-labeling))
         (propagate-constraints v2)
           (cond ((solvable-puzzle-p puzzle2)
              (progn
                (format t "~% The solution is:")
                (show-puzzle (first (search-solutions puzzle2)))
                (format t "~%Solved with ~a guesses." *guesses*)
                ))
                ((impossible-puzzle-p puzzle2)
                 (print-unambiguous-puzzle puzzle))
                (t
                 (print-unambiguous-puzzle puzzle2))))))))

(defun search-unambiguous-puzzle (puzzle)
  "Try all labelings for one ambiguous coordinate, and propagate."
  (if (solvable-puzzle-p puzzle)
      (progn
        (format t "This is an unambiguous puzzle:")
        (show-puzzle puzzle)
        )
       (let* ((v (funcall #'random-ambiguous puzzle)))
         (if (null v)
             (progn
               (format t "~% No more ambiguous coordinates.")
        (show-puzzle puzzle))
      
       (let* ((puzzle2 (make-copy-puzzle puzzle))
              (v2 (find-coordinate (coordinate-name v) puzzle2)))
         (setf v-labeling (random-elt (coordinate-labelings v2)))
         (format t "~% Guessing for coordinate: ~a" (coordinate-name v2))
         (princ (coordinate-labelings v2))
         (format t "~% Guessed : ~a" v-labeling)
         (setf (coordinate-labelings v2) (list v-labeling))
         (propagate-constraints v2)
         (format t "This is an ambiguous puzzle:")
                  (show-puzzle puzzle2)
          (cond ((solvable-puzzle-p puzzle2)
              (progn
                (format t "~% This is an unambiguous puzzle:")
                (show-puzzle puzzle2)
                ;;(setf *unambiguous-puzzle-found* 1)
                ))
                ((impossible-puzzle-p puzzle2)
                 (search-unambiguous-puzzle puzzle))
                (t
                 (search-unambiguous-puzzle puzzle2))))))))
             
;;---------------------------------------------------------------------------------------
;; Display Functions
;;---------------------------------------------------------------------------------------

(defun print-coordinate (coordinate stream depth)
  (declare (ignore stream))
  (declare (ignore stream))
  (format t "~%")
  (format t "Coordinate Name :")
  (princ (coordinate-name coordinate))
  )

(defun show-puzzle (puzzle &optional (title "~2&Puzzle:") (stream t))
  "Print a puzzle in a long form.  Include a title."
  (format stream title)
  (setf width  (+ *aritysq* (- (sqrt *aritysq*) 1)))
  (format t "~%")  
  (dotimes (row *aritysq*)                                                                        ;; Each row contains *aritysq* coordinates
    (setf y-val (+ row 1)) 
    (let ((acc nil))
    (dotimes (col *aritysq*)                                                                      ;; Each coloumn contains *aritysq* coordinates
      (setf x-val (+ 1 col))                                                                      ;; Coordinates start from 1, not 0
      (setf name (+ x-val (* *aritysq* (- y-val 1))))                                             ;; Calculate coordinate-name from x and y values
      (setf coord (find-coordinate name puzzle))                                                  ;; Find corresponding coordinate from the given puzzle
      (cond ((ambiguous-coordinate-p coord) (push "." acc))
            ((impossible-coordinate-p coord) (push "?" acc))
            ((= 1 (number-of-labelings coord)) (push (first (coordinate-labelings coord)) acc))
            (t  (format t "Fatal Error")))
      (if (and (= 0 (second (multiple-value-list 
                             (floor x-val (sqrt *aritysq*))))) (< x-val *aritysq*))
          (push "|" acc)))                                                                        ;; Labels are pushed in LIFO fashion 
      (princ (reverse acc))
      (format t "~% ")     
      (if (and (= 0 (second (multiple-value-list 
                             (floor (+ row 1) (sqrt *aritysq*))))) (< y-val *aritysq*))
    (dotimes (line width)
        (format t "- "))))
   (format t "~%"))
    )

;;------------------------------------------------------------------------------------------
;; Miscellaneous Functions
;;------------------------------------------------------------------------------------------

(defun find-coordinate (name puzzle)
  "Find the coordinate in the given puzzle with the given name."
  (find name (puzzle-coordinates puzzle) :key #'coordinate-name))


(let ((puzzles (make-hash-table)))                                                         

  (defun puzzle (name)
    "Get a fresh copy of the puzzle with this name."
    (make-copy-puzzle (gethash name puzzles)))

  (defun put-puzzle (name puzzle)
    "Store a puzzle under a name."
    (setf (gethash name puzzles) puzzle)
    name))

(defun valid-value-p (value)
  "Check if a given value is valid"
  (if (and (integerp value)                
           (> value 0)
           (< value (+ *aritysq* 1)))
      t))
    
(defun perfect-square-p (n)
  "Check if given number is a perfect square"
  (= (expt (isqrt n) 2)
     n))

(defun make-copy-puzzle (puzzle)                                            
  "Make a copy of a puzzle, preserving connectivity."
  (let* ((new (make-puzzle 
                :coordinates (mapcar #'copy-coordinate
                                  (puzzle-coordinates puzzle)))))
    ;; Put in the neighbors for each coordinate
    (dolist (v (puzzle-coordinates new))
      (setf (coordinate-neighbors v)
            (mapcar #'(lambda (neighbor) 
                        (find-coordinate (coordinate-name neighbor) new))
              (coordinate-neighbors v))))
      new))

(defun find-labelings (puzzle)                                              
  "Return a list of all consistent labelings of the puzzle."
  (every #'propagate-constraints (puzzle-coordinates puzzle))
  (search-solutions puzzle))

(defun random-elt (choices)
  (if (= 0 (length choices))
      nil
    (elt choices (random (length choices)))))

;;---------------------------------------------------------------------------------------------
;; Notes
;;---------------------------------------------------------------------------------------------

;; Initially, I was confused and considered 'd' as arity instead of 'a'.
;; I noticed it very late, and hence modified the code to accept 'a' as arity.
;; So, the variable which was initially *arity* is now *aritysq* to denote the square of arity.