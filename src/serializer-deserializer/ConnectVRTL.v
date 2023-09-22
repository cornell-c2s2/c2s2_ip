`include "../../../C2S2-Module-Library/lib/sim/nbitregister/RegisterV_Reset.v"
`include "../serializer/SerializerVRTL.v"   
`include "../deserializer/DeserializerVRTL.v"  


module ConnectVRTL
   #(
        BIT_WIDTH  = 32,
        N_SAMPLES  = 8
    )(  
        // serializer inputs & outputs
        input  logic [BIT_WIDTH - 1:0] recv_msg                 , 
        input  logic                   recv_val                 ,
        output logic                   recv_rdy                 ,

	    output logic send_val                                   , 
        input  logic send_rdy                                   ,
        output logic [BIT_WIDTH - 1:0] send_msg                 ,

        // clk and reset signals
        input  logic                   reset                    ,
        input  logic                   clk
    );
        // send to serializer
        logic recv_rdys; 
        logic send_vals;
        logic send_rdys;
        logic [BIT_WIDTH - 1:0] send_msgi [N_SAMPLES - 1:0];

        DeserializerVRTL #(.N_SAMPLES(N_SAMPLES), .BIT_WIDTH(BIT_WIDTH)) deserializer
        (
            .recv_val(recv_val), 
            .recv_rdy(recv_rdys), 	 
            .recv_msg(recv_msg),
            .send_val(send_vals), 
            .send_rdy(send_rdy),
            .send_msg(send_msgi),
            .clk(clk), 
            .reset(reset)
        );

        SerializerVRTL #(.N_SAMPLES(N_SAMPLES), .BIT_WIDTH(BIT_WIDTH)) serializer
        (
            .recv_val(send_vals), // output of deserializer
            .recv_rdy(recv_rdy),  // serializer ready to recieve
            .recv_msg(send_msgi), // output of deserializer
            .send_val(send_val), 
            .send_rdy(send_rdys),
            .send_msg(send_msg),
            .clk(clk), 
            .reset(reset)
        );

endmodule
        