module cond_ult53(
    input  [7:0] a,
    input  [7:0] b,
    output [7:0] out
);

    assign out = (a < 8'd53) ? (a & b) : (a ^ b);

endmodule
