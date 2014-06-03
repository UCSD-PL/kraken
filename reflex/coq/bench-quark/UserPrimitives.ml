let create_socket args =
  try
    let socket_desc = (List.nth args 0) in
    let descs = Str.split (Str.regexp ":") socket_desc in
    let host = (List.nth descs 0) in
    let port = int_of_string (List.nth descs 1) in
    let nfamily = int_of_string (List.nth descs 2) in
    let family = (if nfamily = 2 then Unix.PF_INET
                  else if nfamily = 10 then Unix.PF_INET6
                  else Unix.PF_UNIX) in
    let nsocktype = int_of_string (List.nth descs 3) in
    let socktype = (if nsocktype = 1 then Unix.SOCK_STREAM
                    else if nsocktype = 2 then Unix.SOCK_DGRAM
                    else if nsocktype = 3 then Unix.SOCK_RAW
                    else Unix.SOCK_SEQPACKET) in
    let socket = Unix.socket family socktype 0 in
    let ipaddr = (Unix.gethostbyname host).Unix.h_addr_list.(0) in
    let portaddr = Unix.ADDR_INET (ipaddr, port) in
    Unix.connect socket portaddr;
    socket
  with
    _ -> fd_of_int 0

let dom_ok args = ""
(*
  let is_suffix str suffix = 
    (Str.string_match (Str.regexp (String.concat "" (".*"::suffix::[]))) str 0) in
  let socket_desc = (List.nth args 0) in
  let domain = (List.nth args 1) in
  let descs = Str.split (Str.regexp ":") socket_desc in
  let host = (List.nth descs 0) in
  let whitelist = [ ("google.com", ["gstatic.com"]);
                    ("facebook.com", ["fbcdn.net"]);
                    ("youtube.com", ["ytimg.com"]);
                    ("yahoo.com", ["yimg.com"]);
                    ("wikipedia.org", ["wikimedia.org"]);
                    ("twitter.com", ["twimg.com"]);
                    ("ebay.com", ["ebaystatic.com"])] in
   if (is_suffix host domain) then ""
   else if (List.fold_left (fun acc (dmn, whtlst) -> acc ||
                            if (is_suffix domain dmn)
                            then (List.fold_left (fun a whtdmn -> a || (is_suffix host whtdmn)) false whtlst)
                            else false) false whitelist) then ""
   else "error"
*)

let _INVOKE_FD_MAP : (string * (string list -> Unix.file_descr)) list =
  [("create_socket", create_socket)]

let _INVOKE_STR_MAP : (string * (string list -> string)) list =
  [("dom_ok", dom_ok)]

