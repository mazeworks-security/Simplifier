using Mba.Common.MSiMBA;
using Mba.Parsing;
using Mba.Simplifier.Bindings;
using Mba.Simplifier.Minimization;
using Mba.Simplifier.Pipeline;
using Mba.Simplifier.Utility;
using Mba.Utility;
using Microsoft.Z3;
using System.ComponentModel;
using System.Diagnostics;

bool printUsage = false;
uint bitWidth = 64;
bool useEqsat = false;
bool proveEquivalence = false;
string inputText = null;
inputText = "a&(b|c|d|e)";
inputText = "(a&b&c&d)|e";
inputText = "a|b|c|d|e|f|g";
inputText = "a|b";
inputText = "a|b|c";
//inputText = "((d&(-1^(((e&(-1^((f&(-1^g))^g)))^(f&(-1^g)))^g)))^(e&(-1^((f&(-1^g))^g))))";
inputText = "(a|b|c|d|e|f|g)^(a&b&c)";

inputText = "d & a & e ^ (b ^ a ^ c ^ -1) & d ^ e & a ^ e & b ^ e & c ^ (b ^ a) & d & (l & i) ^ d & e & (c ^ b) ^ c & f & g ^ h ^ g & f & (d & c & e) ^ g & f & (b & d & e) ^ g & f & (d & a & e) ^ g & f & (d & a) ^ g & f & (b & d) ^ g & f & (d & c) ^ g & f & (e & a) ^ g & f & (e & b) ^ g & f & (e & c) ^ g & f & a ^ g & f & b ^ d & a & e & h ^ b & d & e & h ^ d & c & e & h ^ c & f & g & h ^ d & a & h ^ b & d & h ^ d & c & h ^ e & a & h ^ d & h ^ i ^ b & d & h & i ^ i & (g & f & (b & d & e)) ^ g & f & (e & c) & h ^ e & h & (c ^ b) ^ h & (g & f & (b & d)) ^ g & f & (d & c) & h ^ g & f & (d & c & e) & i ^ g & f & (d & a) & i ^ i & (g & f & (b & d)) ^ g & f & (e & b) & i ^ g & f & (e & c) & i ^ d & a & e & h & i ^ b & d & e & h & i ^ d & c & e & h & i ^ d & a & e & i ^ b & d & e & i ^ d & a & h & i ^ d & a & i ^ b & d & i ^ d & c & i ^ e & a & i ^ e & b & i ^ d & i ^ i & h ^ (g & f & (e & a) ^ g & f & (e & b)) & h ^ i & h & (e & c) ^ g & f & (d & a & e) & h & l ^ i & h & (g & f & (b & d & e)) ^ g & f & (d & a & e) & h & i ^ (g & f & (d & a & e) ^ g & f & (b & d & e)) & h ^ (g & f & (d & c & e) ^ g & f & (d & a)) & h ^ (g & f & a ^ g & f & b) & h ^ g & f & (d & a) & h & i ^ i & h & (g & f & (b & d)) ^ g & f & (d & c) & h & i ^ g & f & (e & a) & (i & h) ^ g & f & (e & b) & (i & h) ^ i & h & (g & f & (e & c)) ^ l & (g & f & (b & d & e)) ^ g & f & (d & c & e) & l ^ g & f & (d & a) & h & l ^ g & f & (d & c) & h & l ^ g & f & (d & a) & i & l ^ g & f & (e & c) & i & l ^ d & a & e & h & i & l ^ b & d & e & h & i & l ^ d & c & e & h & i & l ^ g & f & (d & a) & l ^ l & (g & f & (b & d)) ^ g & f & (d & c) & l ^ g & f & (e & a) & l ^ g & f & (e & b) & l ^ g & f & (e & c) & l ^ d & a & e & h & l ^ b & d & e & h & l ^ d & c & e & h & l ^ g & f & a & h & l ^ d & a & e & i & l ^ b & d & e & i & l ^ b & d & h & i & l ^ b & d & e & l ^ d & c & e & l ^ (g & f & a ^ g & f & b) & l ^ (c & f & g ^ d & a & h) & l ^ b & d & h & l ^ d & c & h & l ^ e & a & h & l ^ l & (e & h & (c ^ b)) ^ e & a & i & l ^ (b & d ^ (e & a ^ d & c)) & l ^ e & b & l ^ e & c & l ^ d & h & l ^ d & i & l ^ i & h & l ^ d & l ^ (i ^ h) & l ^ (b ^ a) & e & (i & h) ^ l & i & (g & f & (e & a) & h) ^ ((b ^ a ^ c) & e & (g & f) & (d & h & i) ^ -1) & l ^ l & i & (g & f & (b & d) ^ g & f & (d & c)) ^ l & h & (g & f & (e & c)) ^ d & (i & h & c) ^ g & f & (i & h & c) ^ d & c & h & (l & i) ^ (e & b & i ^ d & a) & l ^ (d & h ^ e & c ^ (g & f & b ^ c & f & g)) & i ^ (g & f & (d & c & e) & i ^ g & f & (d & a & e)) & l ^ l & i & (d & c & e) ^ l & i & (g & f & a) ^ l & i & (g & f & b) ^ l & i & (e & c) ^ l & i & (d & h) ^ l & h & (g & f & (b & d & e)) ^ (g & f & (d & c & e) & h ^ g & f & (d & a & e)) & i ^ (g & f & a ^ g & f & b) & h & i ^ (g & f & (d & c & e) & h ^ g & f & (d & a & e) & i) & l ^ l & i & (g & f & (b & d & e)) ^ g & f & (d & a) & h & i & l ^ l & i & (h & (g & f & (b & d))) ^ g & f & (d & c) & h & i & l ^ (g & f & (e & b) ^ g & f & (e & c)) & h & (l & i) ^ l & h & (g & f & (b & d)) ^ l & h & (g & f & (e & a) ^ g & f & (e & b)) ^ l & i & (g & f & (e & a) ^ g & f & (e & b) ^ g & f & a & h) ^ (g & f & b ^ c & f & g) & h & l ^ l & i & (c & f & g ^ d & a & h) ^ l & i & ((g & f & b ^ c & f & g) & h) ^ (b ^ a) & e & (i & h) & l ^ d & (l & i & c) ^ (g & f & (e & a) ^ d & c & e ^ g & f & (d & c) ^ g & f & a) & i ^ (i & h & (e & c) ^ d & a & e) & l";
inputText = "(((~((((((y&x)^(t&x))^(t&y))^x)^y)^t))|(~((((((z&y)^(t&x))^(t&y))^y)^z)^t)))|((~t)&(~z)))";
inputText = "(((t&(((z&y)^x)^z))|((((((y&x)^(z&y))^(t&x))^(t&y))^(t&z))^y))|(((((((z&x)^(z&y))^(t&x))^(t&y))^(t&z))^x)^y))";

inputText = "(x0^x1^x2^x3)&(x3|(x4|x5&x6))|x7|x8|x9";

inputText = "(x4&(((x5&((x0^x1)^x2))&x6)^((x0^x1)^x2)))";

inputText = "(((x5&((x0^x1)^x2))&x6)^((x0^x1)^x2))"; // 0,1,2,5,6

inputText = "x0|x1|x2|x3^(x4|x5|x6&x7)";

inputText = "(a|b|c)^d";
inputText = "(((~((((((y&x)^(t&x))^(t&y))^x)^y)^t))|(~((((((z&y)^(t&x))^(t&y))^y)^z)^t)))|((~t)&(~z)))";
inputText = "(x0^x1^x2^x3)&(x3|(x4|x5&x6))|x7|x8|x9";

inputText = "(((((((((((((((((((a&(~b))&(~c))&(~d))&f)&g)|((((((~a)&b)&(~c))&(~d))&f)&g))|((((((~a)&(~b))&c)&(~d))&f)&g))|(((((a&b)&c)&(~d))&f)&g))|((((a&(~b))&(~c))&(~d))&e))|(((((~a)&b)&(~c))&(~d))&e))|(((((~a)&(~b))&c)&(~d))&e))|((((a&b)&c)&(~d))&e))|((((~a)&(~b))&(~c))&d))|(((a&b)&(~c))&d))|(((a&(~b))&c)&d))|((((~a)&b)&c)&d))|h)|i)|l)";

inputText = "d & a & e ^ (b ^ a ^ c ^ -1) & d ^ e & a ^ e & b ^ e & c ^ (b ^ a) & d & (l & i) ^ d & e & (c ^ b) ^ c & f & g ^ h ^ g & f & (d & c & e) ^ g & f & (b & d & e) ^ g & f & (d & a & e) ^ g & f & (d & a) ^ g & f & (b & d) ^ g & f & (d & c) ^ g & f & (e & a) ^ g & f & (e & b) ^ g & f & (e & c) ^ g & f & a ^ g & f & b ^ d & a & e & h ^ b & d & e & h ^ d & c & e & h ^ c & f & g & h ^ d & a & h ^ b & d & h ^ d & c & h ^ e & a & h ^ d & h ^ i ^ b & d & h & i ^ i & (g & f & (b & d & e)) ^ g & f & (e & c) & h ^ e & h & (c ^ b) ^ h & (g & f & (b & d)) ^ g & f & (d & c) & h ^ g & f & (d & c & e) & i ^ g & f & (d & a) & i ^ i & (g & f & (b & d)) ^ g & f & (e & b) & i ^ g & f & (e & c) & i ^ d & a & e & h & i ^ b & d & e & h & i ^ d & c & e & h & i ^ d & a & e & i ^ b & d & e & i ^ d & a & h & i ^ d & a & i ^ b & d & i ^ d & c & i ^ e & a & i ^ e & b & i ^ d & i ^ i & h ^ (g & f & (e & a) ^ g & f & (e & b)) & h ^ i & h & (e & c) ^ g & f & (d & a & e) & h & l ^ i & h & (g & f & (b & d & e)) ^ g & f & (d & a & e) & h & i ^ (g & f & (d & a & e) ^ g & f & (b & d & e)) & h ^ (g & f & (d & c & e) ^ g & f & (d & a)) & h ^ (g & f & a ^ g & f & b) & h ^ g & f & (d & a) & h & i ^ i & h & (g & f & (b & d)) ^ g & f & (d & c) & h & i ^ g & f & (e & a) & (i & h) ^ g & f & (e & b) & (i & h) ^ i & h & (g & f & (e & c)) ^ l & (g & f & (b & d & e)) ^ g & f & (d & c & e) & l ^ g & f & (d & a) & h & l ^ g & f & (d & c) & h & l ^ g & f & (d & a) & i & l ^ g & f & (e & c) & i & l ^ d & a & e & h & i & l ^ b & d & e & h & i & l ^ d & c & e & h & i & l ^ g & f & (d & a) & l ^ l & (g & f & (b & d)) ^ g & f & (d & c) & l ^ g & f & (e & a) & l ^ g & f & (e & b) & l ^ g & f & (e & c) & l ^ d & a & e & h & l ^ b & d & e & h & l ^ d & c & e & h & l ^ g & f & a & h & l ^ d & a & e & i & l ^ b & d & e & i & l ^ b & d & h & i & l ^ b & d & e & l ^ d & c & e & l ^ (g & f & a ^ g & f & b) & l ^ (c & f & g ^ d & a & h) & l ^ b & d & h & l ^ d & c & h & l ^ e & a & h & l ^ l & (e & h & (c ^ b)) ^ e & a & i & l ^ (b & d ^ (e & a ^ d & c)) & l ^ e & b & l ^ e & c & l ^ d & h & l ^ d & i & l ^ i & h & l ^ d & l ^ (i ^ h) & l ^ (b ^ a) & e & (i & h) ^ l & i & (g & f & (e & a) & h) ^ ((b ^ a ^ c) & e & (g & f) & (d & h & i) ^ -1) & l ^ l & i & (g & f & (b & d) ^ g & f & (d & c)) ^ l & h & (g & f & (e & c)) ^ d & (i & h & c) ^ g & f & (i & h & c) ^ d & c & h & (l & i) ^ (e & b & i ^ d & a) & l ^ (d & h ^ e & c ^ (g & f & b ^ c & f & g)) & i ^ (g & f & (d & c & e) & i ^ g & f & (d & a & e)) & l ^ l & i & (d & c & e) ^ l & i & (g & f & a) ^ l & i & (g & f & b) ^ l & i & (e & c) ^ l & i & (d & h) ^ l & h & (g & f & (b & d & e)) ^ (g & f & (d & c & e) & h ^ g & f & (d & a & e)) & i ^ (g & f & a ^ g & f & b) & h & i ^ (g & f & (d & c & e) & h ^ g & f & (d & a & e) & i) & l ^ l & i & (g & f & (b & d & e)) ^ g & f & (d & a) & h & i & l ^ l & i & (h & (g & f & (b & d))) ^ g & f & (d & c) & h & i & l ^ (g & f & (e & b) ^ g & f & (e & c)) & h & (l & i) ^ l & h & (g & f & (b & d)) ^ l & h & (g & f & (e & a) ^ g & f & (e & b)) ^ l & i & (g & f & (e & a) ^ g & f & (e & b) ^ g & f & a & h) ^ (g & f & b ^ c & f & g) & h & l ^ l & i & (c & f & g ^ d & a & h) ^ l & i & ((g & f & b ^ c & f & g) & h) ^ (b ^ a) & e & (i & h) & l ^ d & (l & i & c) ^ (g & f & (e & a) ^ d & c & e ^ g & f & (d & c) ^ g & f & a) & i ^ (i & h & (e & c) ^ d & a & e) & l";

inputText = "((((e&((a^b)^c))|((f&((a^b)^c))&g))|((h|i)|l))^(d&(((((h&(((~((a^b)^c))^((f&((a^b)^c))&g))^(e&(((f&((a^b)^c))&g)^((a^b)^c)))))|(i&(((~((a^b)^c))^((f&((a^b)^c))&g))^(e&(((f&((a^b)^c))&g)^((a^b)^c))))))|(l&((((f&((a^b)^c))&g)|(e&((a^b)^c)))^(~((a^b)^c)))))^(((f&((a^b)^c))&g)|(e&((a^b)^c))))^(~((a^b)^c)))))";

inputText = "(x0^x1^x2^x3)&(x3|(x4|x5&x6))|x7|x8|x9";

inputText = "(a^b)|(c^d)";

//inputText = "a|b|c|d";

//inputText = "a^b^c";

//inputText = "(~((~x0 & ~x1) | ((x0 & ~x3) ^ ~x2 ^ x5) | ((x0 & ~x4) ^ (~x1 & ~x2)) | (x2 & ~x0) | (~x1 & (x2 ^ x4)) | (x2 & ~x4) | ((x3 & (~x0 ^ x1)) ^ ~x0 ^ x2 ^ x4 ^ x6))) | ((x2 & ((x0 & ((x1 & ((x4 & (~x3 ^ x5 ^ x6)) ^ (x7 & (~x3 ^ x6)) ^ (~(x3 & x5)) ^ x6)) ^ (x6 & (~x4 ^ x5 ^ x7)) ^ (x3 & (x4 ^ x5)) ^ (x7 & ~x5) ^ ~x4)) ^ (x1 & ((x4 & (~x3 ^ x5 ^ x6)) ^ (x7 & (~x5 ^ x6)) ^ (~(x3 & x5)) ^ x6)) ^ (x6 & (~x4 ^ x5 ^ x7)) ^ (x3 & (x4 ^ x5)) ^ (x7 & ~x5) ^ ~x4)) ^ (x5 & ~x0 & ((x1 & ((x3 & ~x4) ^ ~x6)) ^ (~x3 & ~x4)))) | ((x0 & ((x1 & ((x4 & ((x2 & (x3 ^ x5 ^ x6)) ^ ~x7)) ^ (x3 & ((x5 & ~x2) ^ x6)) ^ (x6 & ~x5) ^ ~x7)) ^ (x6 & ((x2 & (~x3 ^ x4 ^ x5)) ^ (~x3 & ~x4))) ^ (x4 & ((~(x2 & x3)) ^ x5 ^ x7)) ^ (x5 & ~x2) ^ ~x7)) ^ (x5 & ~x2 & ((x4 & (~x1 ^ x3)) ^ ~x3 ^ (x1 & x6)))) | ((x0 & ((x5 & ((x1 & ((x4 & (~x2 ^ x3)) ^ x6 ^ x7)) ^ (x3 & (~x2 ^ x4 ^ x6)) ^ (~(x2 & x4)) ^ x6 ^ x7)) ^ (x2 & ((x1 & ((x3 & (~x4 ^ x6)) ^ (~(x4 & x6)))) ^ (x3 & ~x6) ^ x6 ^ x7)) ^ (x7 & (~x1 ^ x3 ^ x4)) ^ (x4 & (x1 ^ x3)))) ^ (x1 & ((x2 & ((x3 & (x4 ^ x6 ^ x7)) ^ (x4 & ~x6) ^ ~x5 ^ x7)) ^ (x5 & ((x4 & ~x3) ^ x6 ^ x7)) ^ (x3 & (x4 ^ x7)))) ^ (x3 & ((x4 & ((x2 & ~x6) ^ ~x5 ^ x7)) ^ (x5 & (~x2 ^ x6)))) ^ (x5 & (~x2 ^ x6 ^ (x4 & x7))) ^ (x2 & x4 & (x6 ^ x7))) | (~(((x0 & ~x2) ^ ~x3 ^ x5) | x1 | (x4 ^ x2) | ((x2 & ~x0) ^ x6))) | ((x2 & ((x4 & ((x1 & (x0 ^ x3 ^ x5 ^ x6 ^ x7)) ^ (x0 & (~x5 ^ x6)) ^ (x3 & ~x6) ^ x6 ^ x7)) ^ (x0 & ((x1 & ((~(x3 & x6)) ^ x7)) ^ (~(x5 & x6)) ^ x7)) ^ (x1 & x6 & (x3 ^ x5)))) ^ (x1 & ((x6 & ((x0 & (x3 ^ x4 ^ x5)) ^ (x3 & ~x4) ^ x5)) ^ (x4 & x5 & (~(x0 & x3)))))) | ((x2 & ((x0 & ((x1 & ((x3 & (~x5 ^ x7)) ^ (x4 & ~x5) ^ x5 ^ x6)) ^ (x6 & (~x4 ^ x7)) ^ (x5 & ~x3) ^ ~x4 ^ x7)) ^ (x3 & ((x6 & (~x1 ^ x4 ^ x7)) ^ (x1 & (x4 ^ x5)) ^ ~x4 ^ x5 ^ x7)) ^ (x1 & ((x5 & (~x4 ^ x6)) ^ x4 ^ x6)) ^ (x6 & (~x4 ^ x7)) ^ ~x4 ^ x5 ^ x7)) ^ (x5 & ~x0 & (~x1 ^ x3) & (x4 ^ x6))) | ((x0 & ((x2 & ((x4 & ((x6 & ~x1) ^ ~x3 ^ x5 ^ x7)) ^ (x6 & (~x3 ^ x5)) ^ (~x1 & ~x7))) ^ (x3 & ((x1 & ((~(x4 & x5)) ^ x6 ^ x7)) ^ (~x4 & (~x6 ^ x7)))) ^ (x1 & ((x6 & ~x5) ^ ~x7)) ^ (~x4 & (~x6 ^ x7)))) ^ (x1 & x5 & ~x2 & (x4 ^ x6))) | ((x0 & ((x1 & ((x2 & ((x3 & (x5 ^ x7)) ^ (x6 & ~x4) ^ ~x5 ^ x7)) ^ (x5 & (~x3 ^ x4 ^ x6 ^ x7)) ^ (x6 & (~x3 ^ x4)) ^ ~x7)) ^ (x2 & ((x3 & (~x4 ^ x7)) ^ (x5 & (~x4 ^ x6)) ^ ~x7)) ^ (x5 & ((x3 & (~x4 ^ x6)) ^ ~x7)) ^ (x6 & (~x3 ^ x4)) ^ ~x7)) ^ (x1 & ((x5 & ((x2 & (~x4 ^ x6 ^ x7)) ^ (~x3 & (~x4 ^ x6)))) ^ (x2 & ((x3 & (~x6 ^ x7)) ^ (x4 & x6))) ^ (x4 & x6 & ~x3))) ^ (x4 & ~x7 & (~x2 ^ x3)) ^ (x5 & ~x3 & (~x2 ^ x7))) | ((x0 & ((x1 & ((x2 & ((x3 & (x4 ^ x5 ^ x6)) ^ (x4 & ~x6) ^ x5)) ^ (x3 & (~x5 ^ x7)) ^ (x6 & ~x4) ^ ~x5 ^ x7)) ^ (~x3 & ((x2 & (x4 ^ x5 ^ x6)) ^ (x6 & ~x4) ^ ~x5 ^ x7)))) ^ (x4 & ((x1 & ((x3 & (~x2 ^ x6 ^ x7)) ^ (x2 & ~x6) ^ ~x7)) ^ (x2 & ~x3 & ~x6) ^ (~x3 & ~x7))) ^ (x5 & ~x1 & ~x2 & ~x3) ^ (x1 & x3 & x6 & ~x2)) | ((x0 & ((x1 & ((x3 & (~((x2 & ~x7) ^ (x4 & ~x5)))) ^ (x4 & (~x2 ^ x6)) ^ ~x5 ^ x6 ^ (x2 & x7))) ^ (x2 & ((x6 & (~x3 ^ x5 ^ x7)) ^ (x4 & (x3 ^ x7)) ^ (~(x5 & x7)))) ^ (x3 & ((~(x4 & x5)) ^ x7)) ^ (x4 & (x6 ^ x7)) ^ ~x5 ^ x6)) ^ (x3 & ((x2 & ((x4 & (~x5 ^ x6)) ^ (x1 & (x5 ^ x7)) ^ ~x5 ^ x6)) ^ (x1 & ((x6 & ~x7) ^ ~x4 ^ x5)) ^ (x4 & (x6 ^ x7)) ^ ~x5 ^ x6)) ^ (x2 & ((x5 & ~x1 & ~x7) ^ (~x6 & ~x7))) ^ (x4 & ((x1 & ~x7) ^ (x5 & ~x6) ^ ~x7)) ^ (x5 & x6 & ~x1)) | ((x5 & ((x1 & ((x0 & ((x2 & ~x3) ^ ~x3 ^ x6)) ^ (~x3 & (~x2 ^ x6)))) ^ (x4 & ~x3 & (~x0 ^ x2)) ^ (x6 & ((x0 & ~x2) ^ ~x3)))) ^ (x0 & x3 & ((x1 & (x2 ^ x4 ^ x6 ^ x7)) ^ ((~x4 ^ x7) & (x2 ^ x6))))) | ((x2 & ((x6 & ((x0 & ((x1 & ~x3) ^ ~x4)) ^ (x5 & (~x1 ^ x4)) ^ (x3 & ~x4))) ^ (x1 & ((x0 & ~x4) ^ (x3 & ~x4) ^ x5)) ^ (~x4 & (x0 ^ x3 ^ x5)))) ^ (x0 & ((x1 & ((x4 & (~(x5 & ~x3))) ^ (~(x6 & ~x3)))) ^ (~x4 & ~x6))) ^ (x3 & ~x4 & (~x1 ^ x6)) ^ (x5 & ~x6 & (~x1 ^ x4))) | (~(~x5 | x0 | x2 | x3 | x4)) | ((x0 & ((x2 & ((x1 & ((x3 & (~x6 ^ x7)) ^ (x4 & ~x5) ^ ~x6)) ^ (x3 & (~x5 ^ x6 ^ x7)) ^ (x5 & ~x6) ^ ~x4)) ^ (x6 & ((x1 & (~x3 ^ x5)) ^ (x5 & ~x3) ^ ~x4)) ^ (x1 & (~(x4 & (~(x3 & x5))))) ^ (x5 & ~x3) ^ ~x4)) ^ (x3 & ((x2 & ((x1 & ~x6) ^ ~x5 ^ x6 ^ (x4 & x7))) ^ (x4 & (~x1 ^ x6)) ^ (x5 & ~x6) ^ ~x1 ^ x6)) ^ (x5 & ((x4 & ((x1 & ~x2) ^ ~x2 ^ x6)) ^ (x1 & ~x2) ^ (x2 & x6))) ^ (x1 & x2 & x6 & ~x4)) | (~(~x1 | ~x5 | (x2 ^ x0) | (x4 ^ x0) | x3)) | ((x2 & ((x0 & ((x4 & ((x1 & ~x5) ^ x3 ^ x5 ^ x6 ^ x7)) ^ (x5 & (~x3 ^ x6 ^ x7)) ^ (x6 & ((~(x1 & x3)) ^ x7)) ^ (x1 & x3 & x7))) ^ (x1 & ((x5 & (x3 ^ x6 ^ x7)) ^ (x6 & (x3 ^ x7)) ^ ~x4 ^ x7)) ^ (x4 & ((x3 & ~x5) ^ ~x5 ^ x6)) ^ (x5 & (~x6 ^ x7)) ^ (~x6 & ~x7))) ^ (x0 & ((x6 & ((x3 & (~x1 ^ x4 ^ x5)) ^ (x7 & ~x1) ^ x4 ^ x5)) ^ (x5 & ~x4 & (x1 ^ x3)))) ^ (((x4 & ~x7) ^ (x5 & ~x3)) & (x1 ^ x6))) | (~((~(x4 ^ x1 ^ x0)) | ((x0 & (~(x1 & ~x2))) ^ (x3 & ~x5) ^ (~(x1 & x2)) ^ x5) | (x6 ^ x3 ^ x2) | (x3 & ~x1) | (x0 & x3) | (x2 & x3) | (~x1 & (~x0 ^ x5)) | (x0 & (x1 ^ x5)) | (x2 & (~x0 ^ x1 ^ x5)))) | (~(~x5 | x0 | x1 | x3 | (x6 ^ x2))) | (x1 & x5 & ~x0 & ~x2 & (x4 ^ x6)) | (x0 & x1 & ((x4 & ~x3 & (x5 ^ x6)) ^ (x2 & x6 & ~x3))) | (x5 & ~x3 & (~x0 ^ x2) & (x4 ^ x6)) | (x0 & x2 & x6 & ~x3 & ~x4) | (x1 & ((x6 & ((x3 & ~x2 & (~x0 ^ x4)) ^ (x0 & x4 & ~x2))) ^ (x0 & x4 & x5 & ~x3))) | ((x0 & ((x1 & ((x2 & ((x3 & (~x4 ^ x5)) ^ (x4 & (x5 ^ x6)) ^ x5)) ^ (x6 & (~x3 ^ x7)) ^ (~((x4 & ~x5) ^ (x7 & ~x3))))) ^ (x6 & ((x4 & (~x2 ^ x3)) ^ ~x2 ^ x3 ^ x5 ^ x7)) ^ (x5 & ((x2 & (x3 ^ x4 ^ x7)) ^ (x4 & ~x3))) ^ (x7 & (~(x3 & ~x2))) ^ ~x4)) ^ (x2 & ((x1 & ((x6 & (~x4 ^ x7)) ^ (x5 & ~x7) ^ ~x4 ^ x7)) ^ (x6 & (~x3 ^ x4 ^ x7)) ^ (x4 & ~x5) ^ (x7 & ~x5) ^ ~x3)) ^ (x5 & ((x1 & ((x3 & ~x4) ^ ~x6)) ^ (x3 & ~x4) ^ (x6 & (x4 ^ x7)) ^ ~x7)) ^ (x3 & ~x6 & (x4 ^ x7))) | (x0 & x1 & x2 & x7 & (x3 ^ x5))\r\n";

var printHelp = () =>
{
    Console.WriteLine("Usage: Simplifier.exe");
    Console.WriteLine("Command line input not preceded by the option indicators below are considered to be input expressions. Only one input expression is accepted.");
    Console.WriteLine("Command line options:");
    Console.WriteLine("    -h:        print usage");
    Console.WriteLine("    -b:        specify the bit number of variables (default is 64)");
    Console.WriteLine("    -z:        enable a check for valid simplification using Z3");
    Console.WriteLine("    -e:        enable equality saturation based simplification");
};

for (int i = 0; i < args.Length; i++)
{
    var arg = args[i];
    switch (arg)
    {
        case "-h":
            printUsage = true;
            break;
        case "-b":  
            bitWidth = uint.Parse(args[i + 1]);
            i++;
            break;
        case "-z":
            proveEquivalence = true;
            break;
        case "-e":
            useEqsat = true;
            break;
        default:
            if (inputText != null)
                throw new ArgumentException($"Found more than one expression argument. Received both {inputText} and {args[i]}");
            inputText = args[i];
            break;
    }
}

if (inputText == null || printUsage)
{
    printHelp();
    return;
}

// For now we only support integer widths of up to 64 bits.
const int maxWidth = 64;
if (bitWidth > maxWidth)
    throw new InvalidOperationException($"Received bit width {bitWidth}, which is greater than the max width {maxWidth}");

var ctx = new AstCtx();
AstIdx.ctx = ctx;
var id = RustAstParser.Parse(ctx, inputText, bitWidth);

Console.WriteLine($"\nExpression: {ctx.GetAstString(id)}\n\n\n");

var input = id;
id = ctx.RecursiveSimplify(id);
for (int i = 0; i < 3; i++)
{
    // Apply our simplification procedure.
    var simplifier = new GeneralSimplifier(ctx);
    // Run the simplification pipeline.
    id = simplifier.SimplifyGeneral(id);
    // Try to expand and reduce the polynomial parts(if any exist).
    if(ctx.GetHasPoly(id))
        id = simplifier.ExpandReduce(id);

    if (!useEqsat)
        continue;
    if (bitWidth != 64)
        throw new InvalidOperationException($"Equality saturation is only supported for 64-bit expressions");

    // Apply equality saturation.
    ulong timeout = 2000;
    Console.WriteLine($"Running equality saturation with {timeout}ms timeout...");
    var ast = AstParser.Parse(ctx.GetAstString(id), bitWidth);
    var egg = EqualitySaturation.Run(ast, timeout);
    id = RustAstParser.Parse(ctx, egg.ToString(), bitWidth);

    // Apply term rewriting.
    id = ctx.RecursiveSimplify(id);
    Console.WriteLine($"Eqsat run {i} yielded: {ctx.GetAstString(id)}\n\n");
}


Console.WriteLine($"Simplified to: {ctx.GetAstString(id)}\n\nwith cost: {ctx.GetCost(id)}");

if (!proveEquivalence)
    return;

var z3Ctx = new Context();
var translator = new Z3Translator(ctx, z3Ctx);
var before = translator.Translate(input);
var after = translator.Translate(id);
var solver = z3Ctx.MkSolver("QF_BV");

// Set the maximum timeout to 10 seconds.
var p = z3Ctx.MkParams();
uint solverLimit = 10000;
p.Add("timeout", solverLimit);
solver.Parameters = p;

Console.WriteLine("Proving equivalence...\n");
solver.Add(z3Ctx.MkNot(z3Ctx.MkEq(before, after)));
var check = solver.Check();

var printModel = (Model model) =>
{
    var values = model.Consts.Select(x => $"{x.Key.Name} = {(long)ulong.Parse(model.Eval(x.Value).ToString())}");
    return $"[{String.Join(", ", values)}]";
};

if (check == Status.UNSATISFIABLE)
    Console.WriteLine("Expressions are equivalent.");
else if (check == Status.SATISFIABLE)
    Console.WriteLine($"Expressions are not equivalent. Counterexample:\n{printModel(solver.Model)}");
else
    Console.WriteLine($"Solver timed out - expressions are probably equivalent. Could not find counterexample within {solverLimit}ms");