#include "crt/stdio.bi"
#include "crt/string.bi"
#include "crt/stdlib.bi"

#if defined(__FB_WIN32__) or  defined(__FB_WIN64__)
#include "crt/io.bi"
#include "crt/fcntl.bi"
#endif

declare function main(byval argc as integer, byval argv as zstring ptr ptr) as integer

#if defined(UTILS)

#include "utils.bi"
#include "libmio0.bi"


#endif

#define MIO0_VERSION "0.1"

#define GET_BIT(buf, bit) ((buf)[(bit) \ 8] and (1 shl (7 - ((bit) mod 8))))
 



'// align value to N-byte boundary
#define ALIGN(VAL_, ALIGNMENT_) (((VAL_) + ((ALIGNMENT_) - 1)) and not((ALIGNMENT_) - 1))
#define MIN(A_, B_) iif((A_) < (B_) , (A_) , (B_))
#define MAX(A_, B_) iif((A_) > (B_) , (A_) , (B_))
 




#define _ERROR(args...) fprintf(stderr,  args)
#define _INFO(args...)if (1) then printf(args)

#define MIO0_HEADER_LENGTH 16


type lookback 
   as integer  ptr indexes 
   as integer  allocated 
   as integer  count 
   as integer start 
end type





#define LOOKBACK_COUNT 256
#define LOOKBACK_INIT_SIZE 128

type mio0_header_t
 
   as uinteger dest_size 
   as uinteger comp_offset 
   as uinteger uncomp_offset 
end type

function lookback_init() as lookback ptr 'static

dim lb  as lookback ptr 
lb  = malloc(LOOKBACK_COUNT * sizeof(*lb)) 
   
  dim i as integer = 0
  do while i < LOOKBACK_COUNT
      lb[i].allocated = 128 'LOOKBACK_INIT_SIZE
      lb[i].indexes = malloc(lb[i].allocated * sizeof(*lb[i].indexes)) 
      lb[i].count = 0 
      lb[i].start = 0 
      i+=1

 

   loop
 
 
   
   return lb 
   
end function

sub lookback_free(lb as lookback ptr ) 'static
    
    for i as integer = 0 to LOOKBACK_COUNT -1
    free(lb[i].indexes) 
    next
      
   free(lb)
end sub

'static inline void lookback_push(lookback *lkbk, unsigned char val, int index)
'{
'   lookback *lb = &lkbk[val];
'   if (lb->count == lb->allocated) {
'      lb->allocated *= 4;
'      lb->indexes = realloc(lb->indexes, lb->allocated * sizeof(*lb->indexes));
'   }
'   lb->indexes[lb->count++] = index;
'}


'see how to inline maybe
sub lookback_push(lkbk as lookback ptr,_val as ubyte, index as integer)

	dim as lookback ptr lb = @lkbk[_val]
 
   if lb->count = lb->allocated then
      lb->allocated *= 4
      lb->indexes = realloc(lb->indexes, lb->allocated * sizeof(*lb->indexes))
   end if
   
   lb->indexes[lb->count] = index
    lb->count+=1
end sub





sub PUT_BIT(buf as ubyte ptr,_bit as integer ,_val as integer) 'static
 
   dim as ubyte mask 
   mask = 1 shl (7 - (_bit mod 8))
   dim as uinteger offset 
   offset = _bit \ 8
   buf[offset] = (buf[offset] and not(mask)) or iif(_val, mask , 0)
end sub




'#define read_u32_be(buf) (unsigned int)(((buf)[0] << 24) + ((buf)[1] << 16) + ((buf)[2] << 8) + ((buf)[3]))
'#define write_u32_be(buf, val) do { \
'   (buf)[0] = ((val) >> 24) & 0xFF; \
'   (buf)[1] = ((val) >> 16) & 0xFF; \
'   (buf)[2] = ((val) >> 8) & 0xFF; \
'   (buf)[3] = (val) & 0xFF; \
'} while(0)





'///////////////////////////////////////////////////////////////////////////////////////
function read_u32_be(buf as const ubyte ptr) as uinteger
	return cast(uinteger, (buf[0] shl 24) + (buf[1] shl 16) + (buf[2] shl 8) + buf[3])
end function

sub write_u32_be(buf as ubyte ptr , _val as uinteger)

buf[0] = (_val shr 24) and &HFF
buf[1] = (_val shr 16) and &HFF
buf[2] = (_val shr 8) and &HFF
buf[3] = _val and &HFF



end sub
'///////////////////////////////////////////////////////////////////////////////////


function mio0_decode_header(buf as const ubyte ptr, head as mio0_header_t ptr) as integer

   if (memcmp(buf, @"MIO0", 4) = NULL) then
      head->dest_size = read_u32_be(@buf[4])
      head->comp_offset = read_u32_be(@buf[8])
      head->uncomp_offset = read_u32_be(@buf[12])
      
    '  print head->dest_size
    '  print head->comp_offset
   '   print head->uncomp_offset 
     ' print "//////////////////////////////////////////////"

  '   sleep
      return 1 
   end if
   return 0 


end function







function mio0_encode_header(buf as ubyte ptr, head as const mio0_header_t ptr) as integer

   if (memcmp(buf, @"MIO0", 4) = NULL) then
 	 write_u32_be(@buf[4], head->dest_size)
  	 write_u32_be(@buf[8], head->comp_offset)
   	 write_u32_be(@buf[12], head->uncomp_offset)
     	 return 1 
   end if
   return 0 

end function


'// used to find longest matching stream in buffer
'// buf: buffer
'// start_offset: offset in buf to look back from
'// max_search: max number of bytes to find
'// found_offset: returned offset found (0 if none found)
'// returns max length of matching stream (0 if none found)
function find_longest(buf as const ubyte ptr,start_offset as integer,max_search as integer ,found_offset as integer ptr,lkbk as lookback ptr) as integer 'static
    dim as integer best_length = 0
    dim as integer best_offset = 0
    dim as integer cur_length
    dim as integer search_len
    dim as integer farthest, off, i
    dim as integer lb_idx
    dim as ubyte first: first = buf[start_offset]
    dim as lookback ptr lb: lb = @lkbk[first]
   

   '// buf
   '//  |    off        start                  max
   '//  V     |+i->       |+i->                 |
   '//  |--------------raw-data-----------------|
   '//        |+i->       |      |+i->
   '//                       +cur_length
 
   farthest = MAX(start_offset - 4096, 0) 
 
 
   lb_idx = lb->start: do while lb_idx < lb->count andalso lb->indexes[lb_idx] < farthest:   lb_idx+=1:  loop
   
   lb->start = lb_idx
      
   do while lb_idx < lb->count andalso lb->indexes[lb_idx] < start_offset
   	off = lb->indexes[lb_idx]
   	
  	search_len = MIN(max_search, start_offset - off)
  	i = 0: do while i < search_len
          
           if buf[start_offset + i] <> buf[off + i] then
                 exit do
            end if
        i+=1:loop
  
  cur_length = i
           
	if (cur_length = search_len) then
           '// check at most requested max less current length
           search_len = max_search - cur_length
         
           i = 0:   do while i < search_len
             if buf[start_offset + cur_length + i] <> buf[off + i] then
                exit do
            end if
          i+=1:loop
          cur_length += i
        end if
        
        if cur_length > best_length then     
 	   best_offset = start_offset - off 
           best_length = cur_length
        end if
   lb_idx+=1 :loop
   
   ' // return best reverse offset and length (may be 0)
   *found_offset = best_offset 
   return best_length
end function




function mio0_encode( in as const ubyte ptr,length as uinteger, _out as ubyte ptr) as integer

    dim as ubyte ptr bit_buf
    dim as ubyte ptr comp_buf 
    dim as ubyte ptr uncomp_buf 
    dim as uinteger bit_length
    dim as uinteger comp_offset
    dim as uinteger uncomp_offset
    dim as uinteger bytes_proc = 0
    dim as integer  bytes_written
    dim as integer  bit_idx = 0
    dim as integer  comp_idx = 0
    dim as integer  uncomp_idx = 0
    dim as lookback ptr lookbacks
   
    '  // initialize lookback buffer
   lookbacks = lookback_init()
   
   '   // allocate some temporary buffers worst case size
   bit_buf = malloc((length + 7) \ 8) ' // 1-bit/byte
   comp_buf = malloc(length) ' // 16-bits/2bytes
   uncomp_buf = malloc(length) '// all uncompressed
   memset(bit_buf, 0, (length + 7) \ 8) 
   
   
    '// encode data
   '// special case for first byte
   lookback_push(lookbacks, in[0], 0)
   uncomp_buf[uncomp_idx] = in[0]
   uncomp_idx += 1 
   bytes_proc += 1 
   
   PUT_BIT(bit_buf, bit_idx, 1) 
   bit_idx+=1
 
 do while (bytes_proc < length)
     dim as integer offset
     dim as integer max_length =  MIN(length - bytes_proc, 18)
     dim as integer longest_match = find_longest(in, bytes_proc, max_length, @offset, lookbacks)
     lookback_push(lookbacks, in[bytes_proc], bytes_proc)
     
     if longest_match > 2 then
         
     	 dim as integer lookahead_offset
         '// lookahead to next byte to see if longer match
         dim as integer lookahead_length = MIN(length - bytes_proc - 1, 18)
         dim as integer lookahead_match = find_longest(in, bytes_proc + 1, lookahead_length, @lookahead_offset, lookbacks)         
         if  (longest_match + 1) < lookahead_match then
           ' // uncompressed byte
            uncomp_buf[uncomp_idx] = in[bytes_proc]
            uncomp_idx+=1
            PUT_BIT(bit_buf, bit_idx, 1)
            bytes_proc+=1
            longest_match = lookahead_match 
            offset = lookahead_offset 
            bit_idx+=1
            lookback_push(lookbacks, in[bytes_proc], bytes_proc)
         end if

          '    // first byte already pushed above
          dim i as integer
           
     i = 1:  do while i < longest_match
    
        lookback_push(lookbacks, in[bytes_proc + i], bytes_proc + i)
     
        i+=1: loop
 
       
              '// compressed block
         comp_buf[comp_idx] = (((longest_match - 3) and &H0F) shl 4) or _
                              (((offset - 1) shr 8) and &H0F)
         comp_buf[comp_idx + 1] = (offset - 1) and &HFF
         comp_idx += 2
         PUT_BIT(bit_buf, bit_idx, 0)
        bytes_proc += longest_match
     else
    ' print "HERE INSTEAD"
      '// uncompressed byte
   
         uncomp_buf[uncomp_idx] = in[bytes_proc]
         uncomp_idx+=1
         PUT_BIT(bit_buf, bit_idx, 1)
         bytes_proc+=1
     end if
        
        
        
  bit_idx+=1
 
 loop
 
 
 
 
 
 '///////////////////////
' bit_idx = 7615
 'comp_idx = 7854
 'uncomp_idx = 3688
 '//////////////////////
 
 
 
 
  bit_length = ((bit_idx + 7) \ 8)
  
  
  comp_offset = ALIGN(MIO0_HEADER_LENGTH + bit_length, 4)
  uncomp_offset = comp_offset + comp_idx
  bytes_written = uncomp_offset + uncomp_idx

' printf(!"\n")
   '// output header
   memcpy(_out, @"MIO0", 4)
   write_u32_be(@_out[4], length)
   write_u32_be(@_out[8], comp_offset)
   write_u32_be(@_out[12], uncomp_offset)
   
  ' printf(!"\n")
   
  ' printf(!"MAGIC: %s\n",@"MIO0")
   
  ' printf(!"LENGTH: %i(0x%X)\n",length,length)
  ' printf(!"COMPOFFSET: %i(0x%X)\n",comp_offset,comp_offset)
  ' printf(!"UNCOMPOFFSET: %i(0x%X)\n",uncomp_offset,uncomp_offset)
  ' printf(!"BITLENGTH: %i(0x%X)\n",bit_length,bit_length)
  ' printf(!"\n")
   'printf(!"BITIDX:  %i(0x%X)\n",bit_idx ,bit_idx )
  ' printf(!"COMPIDX:  %i(0x%X)\n",comp_idx ,comp_idx )
  ' printf(!"UNCOMPIDX:  %i(0x%X)\n",uncomp_idx ,uncomp_idx )
 
   
   memcpy(@_out[MIO0_HEADER_LENGTH], bit_buf, bit_length)
   memcpy(@_out[comp_offset], comp_buf, comp_idx)
   memcpy(@_out[uncomp_offset], uncomp_buf, uncomp_idx)

'// free allocated buffers
   free(bit_buf) 
   free(comp_buf) 
   free(uncomp_buf) 
   lookback_free(lookbacks) 

   return bytes_written 

end function



function mio0_open_out_file( out_file as const zstring ptr)  as FILE ptr 'static
   if strcmp(out_file, "-") = 0 then
#if defined(__FB_WIN32__) or  defined(__FB_WIN64__)
      _setmode(_fileno(stdout), _O_BINARY) 
#endif
      return stdout 
    else  
      return fopen(out_file, "wb") 
   end if
end function

function mio0_decode( _in as  const ubyte ptr, _out as ubyte ptr, _end as uinteger ptr ) as integer

   dim as mio0_header_t head 
   dim as uinteger bytes_written = 0 
   dim as integer bit_idx = 0
   dim as  integer comp_idx = 0
   dim as  integer uncomp_idx = 0
   dim as  integer valid 

   '// extract header
   valid = mio0_decode_header(_in, @head)
  ' // verify MIO0 header
   if (valid = null) then
      return -2
   end if
   

   
   'print "VALID"
       dim x as integer = 0
   do while bytes_written < head.dest_size
   
'print "BYTE: "; x
   if GET_BIT(@_in[MIO0_HEADER_LENGTH], bit_idx) then
   
   'print "UNCOMP"
 
     ' print hex(_in[MIO0_HEADER_LENGTH + x],2)
     ' print bin(_in[MIO0_HEADER_LENGTH + x],8)
    '  print bin(GET_BIT(@_in[MIO0_HEADER_LENGTH], bit_idx),8)
 

   
        ' // 1 - pull uncompressed data
        _out[bytes_written] = _in[head.uncomp_offset + uncomp_idx] 
        
       'print "OUT: ";_out[bytes_written]
       '
    '   print "UNCOM_OFFSET_HEX: "; hex(_in[head.uncomp_offset + uncomp_idx],2) 
      'print  head.uncomp_offset
      
         bytes_written+=1
         uncomp_idx+=1
         
    else  
     'print "COMP"
  '  print bit_idx
   
   
      ' print hex(_in[MIO0_HEADER_LENGTH + x],2)
      ' print bin(_in[MIO0_HEADER_LENGTH + x],8)
      ' print bin(GET_BIT(@_in[MIO0_HEADER_LENGTH], bit_idx),8)
 


 
        ' // 0 - read compressed data
        dim as  integer idx 
         dim as  integer length 
        dim as  integer i 
        dim as  const ubyte ptr vals: vals = @_in[head.comp_offset + comp_idx] 
        
         'print "COMP_OFFSET_HEX: "; hex(vals[0],2); hex(vals[1],2)
        
        comp_idx += 2 
          length = ((vals[0] and &HF0) shr 4) + 3
         idx = ((vals[0] and &H0F) shl 8) + vals[1] + 1

   i = 0
   do while i < length
   
     _out[bytes_written] = _out[bytes_written - idx ]
     bytes_written +=1
   
   i+=1
   loop
  
         
      end if
      

 	
 	
 	
   'sleep
   
         
 '    if ((bit_idx + 1) mod 8) = 0  then
'  beep
  ' x+=1
 '  end if
   
   
 	
   bit_idx+=1
   
   loop

   
   
   
   
      if ( _end)  then
      *_end = head.uncomp_offset + uncomp_idx
      end if

   return bytes_written
end function



function mio0_decode_file(in_file as const ubyte ptr, offset as ulong, out_file  as const ubyte ptr)  as integer

dim as mio0_header_t  head

dim as FILE ptr in
dim as FILE ptr _out
dim as ubyte ptr in_buf = NULL 
dim as ubyte ptr out_buf = NULL 
dim as long file_size 
dim as integer ret_val = 0 
dim as size_t bytes_read 
dim as integer bytes_decoded 
dim as integer bytes_written 
dim as integer valid 


in = fopen(in_file, "rb")
if in = null then
	
	return 1
	
end if
 

fseek(in, 0, SEEK_END)
file_size = ftell(in)
in_buf = malloc(file_size - offset)
fseek(in, offset, SEEK_SET)




bytes_read = fread(in_buf, 1, file_size - offset, in)
  if (bytes_read <> file_size - offset) then
      ret_val = 2
      goto free_all 
   end if


valid = mio0_decode_header(in_buf, @head)
if valid = null then
      ret_val = 3
      goto free_all
end if
 
out_buf = malloc(head.dest_size)
 
 
   bytes_decoded = mio0_decode(in_buf, out_buf, NULL)
   if bytes_decoded < 0 then
      ret_val = 3 
      goto free_all 
   end if 



_out = mio0_open_out_file(out_file)
   if _out = NULL then
      ret_val = 4
      goto free_all
   end if

    '// write data to file
   bytes_written = fwrite(out_buf, 1, bytes_decoded, _out)
   if  bytes_written <> bytes_decoded then
      ret_val = 5 
   end if


 

   '// clean up
   if _out <> stdout then
      fclose(_out)
   end if
 '    print "dest_size: "; head.dest_size
   '  print "comp size "; head.comp_offset
   '  print "uncomp offset "; head.uncomp_offset
free_all:


   if out_buf then
  
     free(out_buf)
   end if
   
 
   if in_buf then
      free(in_buf)
   end if
   fclose(in)

return ret_val
end function





function mio0_encode_file( in_file as const ubyte ptr, out_file as const ubyte ptr) as integer

   dim as FILE ptr in
   dim as FILE ptr _out
   dim as ubyte ptr in_buf = NULL 
   dim as ubyte ptr out_buf = NULL 
   dim as size_t file_size 
   dim as size_t bytes_read 
   dim as integer bytes_encoded 
   dim as integer bytes_written 
   dim as integer ret_val = 0 


in = fopen(in_file, "rb")
if in = null then
	
	return 1
	
end if
 

   fseek(in, 0, SEEK_END)
   file_size = ftell(in)
   fseek(in, 0, SEEK_SET)
   in_buf = malloc(file_size)




   '// read bytes
   bytes_read = fread(in_buf, 1, file_size, in) 
   if bytes_read <> file_size then
      ret_val = 2
      goto free_all
  end if




out_buf = malloc(MIO0_HEADER_LENGTH + ((file_size+7)\8) + file_size)

 
 
 
 
 
 
 bytes_encoded = mio0_encode(in_buf, file_size, out_buf)

_out = mio0_open_out_file(out_file)
   if _out = NULL then
      ret_val = 4
      goto free_all
   end if


    '// write data to file
   bytes_written = fwrite(out_buf, 1, bytes_encoded, _out)
   if  bytes_written <> bytes_encoded then
      ret_val = 5 
   end if


   '// clean up
   if _out <> stdout then
      fclose(_out)
   end if

free_all:


   if out_buf then
  
     free(out_buf)
   end if
   
 
   if in_buf then
      free(in_buf)
   end if
   fclose(in)

return ret_val



end function



'// mio0 standalone executable
#ifdef MIO0_STANDALONE
type  arg_config
 
   as zstring ptr in_filename
   as zstring ptr out_filename
   as uinteger offset
   as integer compress 
end type



static shared as arg_config default_config = (NULL,NULL,0,1)
 
 
 
sub print_usage() 'static
   _ERROR(!"Usage: mio0 [-c / -d] [-o OFFSET] FILE [OUTPUT]\n" _
   	!"\n" _
   	!"mio0 v" MIO0_VERSION !": MIO0 compression and decompression tool\n" _     
	!"\n" _
        !"Optional arguments:\n" _
        !" -c           compress raw data into MIO0 (default: compress)\n" _
        !" -d           decompress MIO0 into raw data\n" _
        !" -o OFFSET    starting offset in FILE (default: 0)\n" _
        !"\n" _
        !"File arguments:\n" _
        !" FILE        input file\n" _
        !" [OUTPUT]    output file (default: FILE.out), \"-\" for stdout\n") 
   end' 1

end sub
 
 
 
sub  parse_arguments(byval argc as integer, byval argv as zstring ptr ptr,config as arg_config ptr) 'static
dim as integer i =  0
dim as integer file_count = 0

if argc < 2 then
	print_usage
	end 1
end if

 
i = 1
do while i < argc

if argv[i][0] = asc("-") andalso argv[i][1] <> asc(!"\0") then
 
	select case argv[i][1]


		case "c"
			config->compress = 1
			'print "compress"
		case "d"
			config->compress = 0
			'print "decompress"
		case "o"
			i+=1
			if i >= argc then
				 print_usage
			end if
			 config->offset = strtoul(argv[i], NULL, 0)
		case else
			print_usage
	
       

	end select

else
	select case file_count
	
	    case 0 
               config->in_filename = argv[i] 
               
            case 1 
               config->out_filename = argv[i] 
 
          case else
            print_usage
	end select
	file_count+=1



end if



i+=1

loop


if file_count < 1 then
	print_usage
end if


end sub







function main(byval argc as integer, byval argv as zstring ptr ptr) as integer

	dim out_filename as string * FILENAME_MAX

	dim as integer ret_val

	dim as arg_config config
	
	config = default_config
	parse_arguments(argc,argv,@config)
	if config.out_filename = NULL then
		config.out_filename = @out_filename
		sprintf(config.out_filename, "%s.out", config.in_filename)
	end if
	
	if config.compress then
	
		ret_val = mio0_encode_file(config.in_filename, config.out_filename)
	else
		ret_val = mio0_decode_file(config.in_filename, config.offset, config.out_filename)
		'beep
	end if


 
  'print ret_val
	select case ret_val

	case 1
	_ERROR(!"Error opening input fle \"%s\"\n", config.in_filename)
	case 2
	_ERROR(!"Error reading from input file \"%s\"\n", config.in_filename)
	case 3
	_ERROR(!"Error decoding MIO0 data. Wrong offset (0x%X)?\n",config.offset)
	case 4
	_ERROR(!"Error opening output file \"%s\"\n",config.out_filename)
	case 5
	_ERROR(!"Error writing bytes to output file \"%s\"\n",config.out_filename)
	end select
         

	'sleep 

return ret_val
end function



end main(__FB_ARGC__,__FB_ARGV__)


#endif '// MIO0_STANDALONE







