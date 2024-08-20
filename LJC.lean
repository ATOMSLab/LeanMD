import Lean.Data.Parsec

open Lean Parsec

namespace CSV

/-- CSV Parser Definitions -/
abbrev Field_CSV := String
abbrev Record := Array Field_CSV
abbrev Csv := Array Record

/-- Parser: Parsing a comma-separated value -/
def comma : Parsec Char := pchar ','

/-- Parser: Parsing a newline (CRLF, LF, or CR) -/
def crlf : Parsec String := pstring "\r\n" <|> pstring "\n" <|> pstring "\r"

/-- textData matches characters that are part of the field, including negative signs, digits, and decimals. -/
def textData : Parsec Char := satisfy fun c =>
  c.isDigit || c == '.' || c == '-' || c == 'e' || c == 'E'

/-- cr, lf, and crlf are parsers for carriage return, line feed, and their combination.-/
def cr : Parsec Char := pchar '\r'   -- Carriage Return (used in older Mac systems)-/
def lf : Parsec Char := pchar '\n'   -- Line Feed (used in Unix/Linux and modern Mac systems)-/


/-- dQUOTE matches a double quote character, which is used to escape fields in a Csv file.-/
def dQUOTE : Parsec Char := pchar '\"'

/-- twoDQUOTE matches two consecutive double quotes "", which represent an escaped double quote within a quoted field.-/
def twoDQUOTE  : Parsec Char := attempt (pchar '"' *> pchar '"')

/-- escaped matches fields surrounded by double quotes.
-- It allows for more complex data inside the field, such as commas and newlines.-/
def escaped : Parsec String := attempt
  dQUOTE *>   -- Start with an opening double quote
  manyChars (textData <|> comma <|> cr <|> lf <|> twoDQUOTE) -- Allow special characters
  <* dQUOTE  -- End with a closing double quote

/-- nonEscaped is for fields that are not enclosed in double quotes.
  It matches a series of valid characters that do not include special characters like commas or newlines.-/
def nonEscaped: Parsec String := manyChars textData

/-- field is a parser that can handle both escaped and non-escaped fields.-
    It uses the escaped parser first and if that fails, it tries nonEscaped.-/
def field : Parsec Field_CSV := escaped <|> nonEscaped

/--
  manySep is a higher-order parser that matches many occurrences of a pattern p
  separated by a separator s.
  For example, in a CSV file, fields are separated by commas.
  This function returns an array of parsed elements.
-/
def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

/-- record parses a single row of CSV, which is a sequence of fields separated by commas.-/
def record : Parsec Record := manySep field comma

/-- file parses the entire CSV file, which consists of multiple records separated by newlines.-/
def file : Parsec $ Array Record :=
  manySep record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

/-- parse is a function that takes a string (the content of a CSV file) and returns either
    the parsed data successfully or an error message.-/
def parse (s : String) : Except String $ Array $ Array $ String :=
  match file s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res  -- Return the result if successful
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"  -- Return an error message

-- e.g., let's parse a CSV string directly.

#eval parse ("1.0771699,-1.0209881,-1.3482594\n0.1830885,-1.5576982,-1.7824055\n-2.0603462,3.9273783,3.8895551")

/--
  manyHomoCore is a parser that ensures all parsed arrays have the same size.
  This is useful for validating that every row in a CSV file has the same number of fields,
  which is often a requirement for properly formatted CSV files.
-/
partial def manyHomoCore (p : Parsec $ Array α) (acc : Array $ Array α) : Parsec $ Array $ Array α :=
  (do
    let first ← p
    if acc.size = 0 then
      manyHomoCore p (acc.push first)  -- If it's the first element, it just adds it
    else
      if acc.back.size = first.size then
        manyHomoCore p (acc.push first)  -- If the sizes match, parsing continues
      else
        fail "expect same size"  -- If sizes don't match, error thrown
  )
  <|> pure acc  -- If parsing fails, it returns the accumulated result

/--
  manySepHomo parses many arrays of p with the same size separated by s.
  It is used to parse a CSV file while making sure that all rows have the same number of fields ensuring uniformity.
-/
def manySepHomo (p : Parsec $ Array α) (s : Parsec β) : Parsec $  Array $ Array α := do
  manyHomoCore (attempt (s *> p)) #[←p]

/-- file' is an alternative CSV file parser most likely.
    It ensures each row has the same number of fields.-/
def file' : Parsec $ Array Record := manySepHomo record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

/-- parse' is a function that parses a string with an additional check for homogeneous field counts across records.-/
def parse' (s : String) : Except String $ Array $ Array $ String :=
  match file' s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res  -- Return the result if successful
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"  -- Return an error message

/-This is by me, John Velkey.-/
  /-John's function to handle exceptions -/
/-- This function handles the result of the CSV parsing and returns either the parsed data or an error message.
    If parsing fails, it returns a default error message.-/
def CSVParseExceptHandler (inputParse : Except String (Array (Array String))) : Array $ Array $ String :=
  match inputParse with
  | Except.ok α => α   -- If parsing is successful, return the result
  | Except.error _ => #[#["CSV Parse Error"]]  -- If there's an error, return a default error message

def CSVParseIt : IO Unit := do
  -- Read through of the CSV file
  let fileContent ← IO.FS.readFile "data_for_LJC.csv"

  -- Parse the file using the parse function
  let parsedCSV := parse fileContent

  -- Handles the result using the CSVParseExceptHandler function
  let result := CSVParseExceptHandler parsedCSV

  IO.println result




#eval CSVParseIt


set_option maxHeartbeats 10000000

def ListDiv (L1 : List Float) (L2 : List Float) : List Float :=
  match L1, L2 with
  | [], [] => []
  | L1h :: L1t, L2h :: L2t => (L1h / L2h) :: (ListDiv L1t L2t)
  | _, _ => []

def ListProd (L1 : List Float) (L2 : List Float) : List Float :=
  match L1, L2 with
  | [], [] => []
  | L1h :: L1t, L2h :: L2t => (L1h * L2h) :: (ListProd L1t L2t)
  | _, _ => []

def listSub (L1 : List Float) (L2 : List Float) : List Float :=
  match L1, L2 with
  | [], [] => []
  | L1h :: L1t, L2h :: L2t => (L1h - L2h) :: (listSub L1t L2t)
  | _, _ => []

def apply_pbc (position : List Float) (cell_length : List Float) : List Float :=
  let div_result := ListDiv position cell_length
  let round_result := div_result.map (λ x => Float.round x)
  let prod_result := ListProd cell_length round_result
  listSub position prod_result


def minimum_image_distance (r_ij : List Float) (cell_length : List Float) : List Float :=
  let div_result := ListDiv r_ij cell_length
  let round_result := div_result.map (λ x => Float.round x)
  let prod_result := ListProd cell_length round_result
  let result := listSub r_ij prod_result
  result

def vectorNorm (vector : List Float) : Float :=
  (vector.foldr (λ x acc => x ^ 2 + acc) 0.0).sqrt

def lennard_jones_potential (r : Float) (cutoff : Float) : Float :=
  if r < cutoff then
    let epsilon := 1.0
    let sigma := 1.0
    let r6 := (sigma / r) ^ 6
    let r12 := r6 * r6
    4 * epsilon * (r12 - r6)
  else
    0.0

-- Recursive Helper Function
def energy (positions : List (List Float)) (cell_length : List Float) (cutoff : Float) (i j : Nat) (accumulated_energy : Float) : Float :=
  if i = 0 then
    accumulated_energy
  else if j = 0 then
    energy positions cell_length cutoff (i - 1) (i - 2) accumulated_energy
  else
    let r_ij := listSub (positions[i - 1]!) (positions[j - 1]!)
    let r_ij1 := apply_pbc r_ij cell_length
    let r_ij2 := minimum_image_distance r_ij1 cell_length
    let distance := vectorNorm r_ij2
    let energy_contrib := lennard_jones_potential distance cutoff
    energy positions cell_length cutoff i (j - 1) (accumulated_energy + energy_contrib)

def compute_energy (positions : List (List Float)) (cell_length : List Float) (cutoff : Float := 3.0) : Float :=
  let num_atoms := positions.length
  energy positions cell_length cutoff num_atoms (num_atoms - 1) 0.0


def cell_length : List Float := [8.0, 8.0, 8.0]

def positions : List (List Float) :=
[
  [1.077169909511, -1.020988125886, -1.348259447733],
  [0.1830884592213, -1.557698231574, -1.782405485883],
  [-2.060346185437, 3.927378276290, 3.889555115290],
  [1.936298049102, 0.7181973326223, 3.715169082037],
  [-0.7514139041700, -0.4184139469527, -3.250183630687],
  [2.257391305584, -1.126577405146, -2.291542913197],
  [0.1208868721243, -1.395611520000, 2.003709382777],
  [3.327427055092, -1.476502868105, 3.394023898450],
  [2.130927328546, -1.106827632561, -0.1972896367169],
  [2.117442019559, -0.1844743512029, 0.9301638993772],
  [-1.459378119580, 2.382882188329, -3.788199401470],
  [2.432313424884, -1.118537915440, -1.224088264651],
  [2.416845366530, 1.845499053895, 2.906107003288],
  [2.515247912050, 0.03580976978134, -2.445590080636],
  [1.113585242376, -2.478011342991, -0.008092189527960],
  [1.261664073561, 1.075432348722, -2.751715752259],
  [-0.5811873476022, -2.429378395199, 2.668996832737],
  [-1.533182296119, 2.319699660489, 1.762429379767],
  [2.639946585704, -0.7847515599358, 2.251233247739],
  [-1.927486378623, -1.432729425739, -2.439226375584],
  [0.9212801355440, -2.427925517025, 2.150024430246],
  [2.114172305774, 0.9586575168591, -1.790678078404],
  [-0.7312380271746, -3.366157234697, 0.1376597954432],
  [1.612569300954, -0.9233415846164, 2.037484769332],
  [3.967911812136, 0.2002508998947, 2.659432175592],
  [1.188751191387, -0.05955638413419, -0.7363070447875],
  [3.789497702433, 1.570674334424, 0.7265918374820],
  [2.786625773109, -1.524167484397, 0.8358187540631],
  [-1.629362446504, -1.139061532617, -0.7654084051377],
  [2.592655226763, 3.786335083587, -1.252452130644]
]


#eval compute_energy positions cell_length
