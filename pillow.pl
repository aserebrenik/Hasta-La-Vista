% *** pillow.pl *** Version 1.0b
% A Simple HTTP Package for Prolog and CLP systems
% To be used with html.pl 96.2.1b
% 
% Copyright (C) 1996 UPM-CLIP.
% 
% This package is free software; you can redistribute it and/or
% modify it under the terms of the GNU Library General Public
% License as published by the Free Software Foundation; either
% version 2 of the License, or (at your option) any later version.
% 
% This package is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
% Library General Public License for more details.
% 
% You should have received a copy of the GNU Library General Public
% License along with this package; if not, write to the Free
% Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
% 
% M. Hermenegildo (herme@fi.upm.es), D. Cabeza (dcabeza@fi.upm.es) and
% S. Varma (sacha@clip.dia.fi.upm.es)

:- module(pillow,
        [fetch_url/3, % The rest are from html.pl ...
         url_info/2, url_info_relative/3, url_query/2,
         output_html/1, html2terms/2, html_report_error/1,
         get_form_input/1, get_form_value/3, form_empty_value/1,
         form_default/3, my_url/1, form_request_method/1,
         icon_address/2,
         save_cgi_bin/2, save_cgi/2, html_protect/1]).

pillow_version("1.0b").

:- ensure_loaded(html).

% ============================================================================
% fetch_url(+URL,+Request,-Response)
%
% Fetch a document from an HTTP server
%
% `Request' is a list which may contain:
% * head - If we don't what the document, only the heading
% * timeout(integer) - Time to wait for the response
% * if_modified_since(date) - Get document only if newer
% * user_agent(atom) - Provide a user-agent field
% * authorization(scheme,params) - ...
% * f(atom) - Any other option (for example from('user@machine').
%
% `Response' is a list which may contain:
% * content(string) - Document content
% * status(atom,integer,string) - Type of response, status code and reason
%     phrase
% * pragma(string) - Misc. data
% * message_date(date) - Date of the response
% * location(atom) - Where has moved the document
% * http_server(string) - Server responding
% * authenticate(..) - Returned if document is protected
% * allow(list(atom)) - Methods allowed by the server
% * content_encoding(atom)
% * content_length(integer)
% * content_type(atom,atom,list(atom=(atom|string))) -
% * expires(date) - Date/time after which the entity should be considered stale
% * last_modified(date) - date and time at which the sender believes the
%     resource was last modified 
% * f(string) - Any other functor `f' is an extension header

% Notes: Does not support proxies. Fails on timeout.


fetch_url(http(Host, Port, Document), Request, Response) :-
    timeout_option(Request, Timeout, Request1),
    http_request(Document, Request1, RequestChars, []), !,
    http_transaction(Host, Port, RequestChars, Timeout, ResponseChars),
    http_response(Response, ResponseChars, []).

% ============================================================================
% timeout_option(+Options, -Timeout, -RestOptions)
% 
% Returns timeout option, by default 5 min. (300s).
% ============================================================================

timeout_option(Options, Timeout, RestOptions) :-
        select(timeout(Timeout), Options, RestOptions), !.
timeout_option(Options, 300, Options).

% ============================================================================
% http_request(+Document, +Request, -RequestChars, -RequestCharsTail)
% 
% Generate an HTTP request from a list of parameters
%
% Notes: 
%
%        Conforms to RFC 1945 guidelines
%        Does not use the headers:
%          current date
%          pragma
%          referer
%          entity body
%              (this will have to change if the implementation
%               extends beyond the GET and HEAD methods.
%               cf RFC1945 section 7.2)
% ============================================================================

http_request(Document,Options) -->
        http_request_method(Options,Options1),
        " ",
        string(Document),
        " HTTP/1.0",
        http_crlf,
        http_req(Options1), !.

http_request_method(Options,Options1) -->
        {
            select(head, Options, Options1)
        }, !,
        "HEAD".
http_request_method(Options, Options) -->
        "GET".

http_req([]) -->  http_crlf.
http_req([Option|Options]) -->
        http_request_option(Option), !,
        http_req(Options).

http_request_option(user_agent(A)) --> !,
        {
            atom_chars(A,AStr),
            pillow_version(Ver)
        },
        "User-Agent: ",
        string(AStr),
        " PiLLoW/",
        string(Ver),
        http_crlf.
http_request_option(if_modified_since(date(WkDay,Day,Month,Year,Time))) --> !,
        "If-Modified-Since: ",
        http_internet_date(WkDay,Day,Month,Year,Time),
        http_crlf.
http_request_option(authorization(Scheme, Params)) --> !,
        "Authorization: ",
        http_credentials(Scheme, Params),
        http_crlf.
http_request_option(O) -->
        {
            functor(O,F,1),
            atom_chars(F,FS),
            arg(1,O,A),
            atom_chars(A,AS)
        }, !,
        string(FS),
        ": ",
        string(AS),
        http_crlf.
http_request_option(_) --> "". % Perhaps give a warning?

http_credentials(basic, Cookie) --> !,
        "Basic ",
        string(Cookie).
http_credentials(Scheme,Params) --> !,
        {
            atom_chars(Scheme, S)
        },
        string(S), " ",
        http_credential_params(Params).

http_credential_params([]) --> "".
http_credential_params([P|Ps]) -->
        http_credential_param(P),
        http_credential_params_rest(Ps).
http_credential_params_rest([]) --> "".
http_credential_params_rest([P|Ps]) -->
        ", ",
        http_credential_param(P),
        http_credential_params_rest(Ps).

http_credential_param(P=V) -->
        {
            atom_chars(P,PS)
        },
        string(PS), "=""", string(V), """".

% ============================================================================
% PROLOG BNF GRAMMAR FOR HTTP RESPONSES
%  Based on RFC 1945
%
% ============================================================================


http_response(R) -->
	http_full_response(R), !.
http_response(R) -->
	http_simple_response(R).

http_full_response([Status|Head_Body]) -->
        http_status_line(Status),
        http_response_headers(Head_Body,Body),
        http_crlf,
        http_entity_body(Body).

http_simple_response(Body) -->
        http_entity_body(Body).

http_response_headers([H|Hs], Hs_) -->
        http_response_header(H), !,
        http_response_headers(Hs, Hs_).
http_response_headers(Hs, Hs) --> "".

http_entity_body([content(B)],B,[]).

% ----------------------------------------------------------------------------

http_status_line(status(Ty,SC,RP)) -->
        "HTTP/", parse_integer(_Major), ".", parse_integer(_Minor),
        http_sp,
        http_status_code(Ty,SC),
        http_sp,
        http_line(RP), !.

http_status_code(Ty,SC) -->
        [X,Y,Z],
        {
            type_of_status_code(X,Ty), !,
            number_chars(SC,[X,Y,Z])
        }.

type_of_status_code(0'1, informational).
type_of_status_code(0'2, success).
type_of_status_code(0'3, redirection).
type_of_status_code(0'4, request_error).
type_of_status_code(0'5, server_error).
type_of_status_code(_, extension_code).

% ----------------------------------------------------------------------------

% General header
http_response_header(P) --> http_pragma(P).
http_response_header(D) --> http_message_date(D).
% Response header
http_response_header(L) --> http_location(L).
http_response_header(S) --> http_server(S).
http_response_header(A) --> http_authenticate(A).
% Entity header
http_response_header(A) --> http_allow(A).
http_response_header(E) --> http_content_encoding(E).
http_response_header(L) --> http_content_length(L).
http_response_header(T) --> http_content_type(T).
http_response_header(X) --> http_expires(X).
http_response_header(M) --> http_last_modified(M).
http_response_header(E) --> http_extension_header(E).

% ----------------------------------------------------------------------------

http_pragma(pragma(P)) -->
        http_field("pragma"),
        http_line(P).

http_message_date(message_date(D)) -->
        http_field("date"),
        http_date(D),
        http_crlf.

http_location(location(URL)) -->
        http_field("location"),
        http_line(URLStr),
        {
            atom_chars(URL,URLStr)
        }.

http_server(http_server(S)) -->
        http_field("server"),
        http_line(S).

http_authenticate(authenticate(C)) -->
        http_field("www-authenticate"),
        http_challenges(C).

http_allow(allow(Methods)) -->
        http_field("allow"),
        http_token_list(Methods),
        http_crlf.

http_content_encoding(content_encoding(E)) -->
        http_field("content-encoding"),
        http_lo_up_token(E),
        http_lws0,
        http_crlf.

http_content_length(content_length(L)) -->
        http_field("content-length"),
        parse_integer(L),
        http_lws0,
        http_crlf.

http_content_type(content_type(Type,SubType,Params)) -->
        http_field("content-type"),
        http_media_type(Type,SubType,Params),
        http_crlf.

http_expires(expires(D)) -->
        http_field("expires"),
        http_date(D),
        http_crlf.

http_last_modified(last_modified(D)) -->
        http_field("last-modified"),
        http_date(D),
        http_crlf.

http_extension_header(T) -->
        http_field(F),
        http_line(A),
        {
            atom_chars(Fu,F),
            functor(T,Fu,1),
            arg(1,T,A)
        }.
% ----------------------------------------------------------------------------

http_date(date(WeekDay,Day,Month,Year,Time)) -->
        http_internet_date(WeekDay,Day,Month,Year,Time)
 ;
        http_asctime_date(WeekDay,Day,Month,Year,Time).

http_internet_date(WeekDay,Day,Month,Year,Time) -->
        http_weekday(WeekDay),
        ",",
        http_sp,
        http_day(Day),
        (http_sp ; "-"),
        http_month(Month),
        (http_sp ; "-"),
        http_year(Year),
        http_sp,
        http_time(Time),
        http_sp,
        "GMT".

http_asctime_date(WeekDay,Day,Month,Year,Time) -->
        http_weekday(WeekDay),
        http_sp,
        http_month(Month),
        http_sp,
        http_day(Day),
        http_sp,
        http_time(Time),
        http_sp,
        http_year(Year).

http_weekday('Monday') --> "Mon".
http_weekday('Tuesday') --> "Tue".
http_weekday('Wednesday') --> "Wed".
http_weekday('Thursday') --> "Thu".
http_weekday('Friday') --> "Fri".
http_weekday('Saturday') --> "Sat".
http_weekday('Sunday') --> "Sun".
http_weekday('Monday') --> "Monday".
http_weekday('Tuesday') --> "Tuesday".
http_weekday('Wednesday') --> "Wednesday".
http_weekday('Thursday') --> "Thursday".
http_weekday('Friday') --> "Friday".
http_weekday('Saturday') --> "Saturday".
http_weekday('Sunday') --> "Sunday".

http_day(Day) -->
        [D1,D2],
        {
            number_chars(Day,[D1,D2])
        }.
http_day(Day) -->
        [0'0,D2],
        {
            number_chars(Day,[D2])
        }.
http_day(Day) -->
        http_sp,
        [D],
        { 
            number_chars(Day,[D])
        }.

http_month('January') --> "Jan".
http_month('February') --> "Feb".
http_month('March') --> "Mar".
http_month('April') --> "Apr".
http_month('May') --> "May".
http_month('June') --> "Jun".
http_month('July') --> "Jul".
http_month('August') --> "Aug".
http_month('September') --> "Sep".
http_month('October') --> "Oct".
http_month('November') --> "Nov".
http_month('December') --> "Dec".

% Assumes Year > 999
http_year(Year) -->
        [Y1,Y2,Y3,Y4],
        {
            number_chars(Year,[Y1,Y2,Y3,Y4])
        }.
http_year(Year) -->
        [Y1,Y2],
        {
            number_chars(Y,[Y1,Y2]),
            ( Y >= 70 -> Year is 1900+Y ; Year is 2000+Y )
        }.

http_time(Time) -->
        [H1,H2,0':,M1,M2,0':,S1,S2],
        {
            atom_chars(Time,[H1,H2,0':,M1,M2,0':,S1,S2])
        }.


% ----------------------------------------------------------------------------

http_challenges([C|CS]) -->
        http_maybe_commas,
        http_challenge(C),
        http_more_challenges(CS).

http_more_challenges([C|CS]) -->
        http_commas,
        http_challenge(C),
        http_more_challenges(CS).
http_more_challenges([]) --> http_lws0, http_crlf.

http_challenge(challenge(Scheme,Realm,Params)) -->
        http_lo_up_token(Scheme),
        http_sp,
        http_lo_up_token(realm), "=", http_quoted_string(Realm),
        http_lws0,
        http_auth_params(Params).

http_auth_params([P|Ps]) -->
        ",", http_lws0,
        http_auth_param(P), http_lws0,
        http_auth_params(Ps).
http_auth_params([]) --> "".

http_auth_param(P=V) -->
        http_lo_up_token(P),
        "=",
        http_quoted_string(V).

% ----------------------------------------------------------------------------

http_token_list([T|Ts]) -->
        http_maybe_commas,
        http_token(T),
        http_token_list0(Ts).

http_token_list0([T|Ts]) -->
        http_commas,
        http_token(T),
        http_token_list0(Ts).
http_token_list0([]) -->
        http_maybe_commas.

http_commas -->
        http_lws0,",",http_lws0,
        http_maybe_commas.

http_maybe_commas --> "".
http_maybe_commas -->
        ",", http_lws0,
        http_maybe_commas.



% ----------------------------------------------------------------------------

http_field([C|Cs]) -->
        http_lo_up_token_char(C),
        http_lo_up_token_rest(Cs),
        ":", http_lws.

% ----------------------------------------------------------------------------

select(X,[X|L],L).
select(X,[Y|L],[Y|L2]) :-
        select(X,L,L2).

% ============================================================================
% http_transaction(+Host, +Port, +Request, +Timeout, -Response)
% type http_transaction(atom, integer, string, integer, string).
%
% Notes: Sends an HTTP Request to an HTTP server and returns the
%         resultant message in Response
% 
%        Fails on timeout (Timeout in seconds) 
% ============================================================================

:- use_module(library(sockets)).

http_transaction(Host, Port, Request, Timeout, Response) :-
        socket('AF_INET', Socket),
        socket_connect(Socket, 'AF_INET'(Host,Port), Stream),
        write_string(Request,Stream),
        flush_output(Stream),
        stream_select([Stream],Timeout:0,R),
        R \== [],  % Fail if timeout
        read_to_close(Stream, Response).

write_string([],_).
write_string([C|Cs],S) :- put(S,C), write_string(Cs,S).

        
read_to_close(S, L) :-
        get0(S, C),
        read_to_close1(C, S, L).

read_to_close1(-1, _, []) :- !.
read_to_close1(C, S, [C|L]) :-
        get0(S, C1),
        read_to_close1(C1, S, L).
