// =================================================================================
// Author: Johnny Martinez
// Date: 02/16/2025
// Documentation: https://confluence.cornell.edu/display/c2s2/Tapein1+-+Goose
//
// Spec:
// PARAMETERS ----------------------------------------------------------------------
// I/O -----------------------------------------------------------------------------
// =================================================================================

// Progress:
// Added all blocks for tapein-1 (excluding lbist). I need to address TODOs and
// work out routing logic.

`ifndef TAPEIN1_SP25_TOP_V
`define TAPEIN1_SP25_TOP_V

`include "spi/minion.v"
`include "arbiter_router/router.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"
`include "arbiter_router/arbiter.v"
`include "arbiter_router/router.v"
`include "crossbars/blocking.v"
`include "classifier/classifier.v"
`include "wishbone/wishbone.v"

module tapein1_sp25_top(

  // Clock and Reset Ports
  input  logic  clk,
  input  logic  reset,

  // SPI Minion ports
  input  logic  cs,
  input  logic  mosi,
  output logic  miso,
  input  logic  sclk,
  output logic  minion_parity,
  output logic  adapter_parity,

  // Wishbone Slave ports (WB MI A)
  input  logic         wbs_stb_i,
  input  logic         wbs_cyc_i,
  input  logic         wbs_we_i,
  input  logic [3:0]   wbs_sel_i,
  input  logic [31:0]  wbs_dat_i,
  input  logic [31:0]  wbs_adr_i,
  output logic         wbs_ack_o,
  output logic [31:0]  wbs_dat_o,

  // These outputs are necessary to set the valid
  // io_oeb and io_out values for the gpios.

  // TODO how to set GPIO?
  output logic [22:0] io_oeb,
  output logic [4:0] io_out
);

  // TODO: What does this do?
  // io_oeb can always be zero as we are using inputs with nopull
  assign io_oeb = 0;
  // gpios 0-4 require output values to be set.
  assign io_out = 0;

  // TODO: If there are unused bits, we need to use them arbitarily somehow to avoid linter errors and such

  //============================LOCAL_PARAMETERS====================================
  // SPI Minion --------------------------------------------------------------------
  // - ADDR_BITS:
  //     Bitwidth of address bits in SPI input packet. Note, address bits compose
  //     MSBs of input packet.
  // - DATA_BITS:
  //     Bitwidth of data bits in SPI input packet.
  // SPI Packet
  //  19  18  17  16  15  14  13  12  11  10  09  08  07  06  05  04  03  02  01  00
  // ------------------------------------------------------------------------------
  // | ADDRESS     |                             DATA                             |
  // ------------------------------------------------------------------------------
  localparam int ADDR_BITS   = 4;
  localparam int DATA_BITS   = 16;
  localparam int SPI_PACKET_BITS = DATA_BITS + ADDR_BITS;

  // Router ------------------------------------------------------------------------
  // - ROUTER_SIZE:
  //     Number of router output ports.
  // - ROUTER_PACKET_BITS:
  //     Bitwidth of data bits in router input/output packets.
  localparam int ROUTER_SIZE = 1 << ADDR_BITS;
  localparam int ROUTER_PACKET_BITS = DATA_BITS + ADDR_BITS;


  // Arbiter -----------------------------------------------------------------------
  // - ARBITER_SIZE:
  //     Number of arbiter output ports.
  // - ARBITER_PACKET_BITS:
  //     Bitwidth of data bits in arbiter input/output packets.
  localparam int ARBITER_SIZE = ROUTER_SIZE;
  localparam int ARBITER_PACKET_BITS = DATA_BITS;


  // Input Xbar --------------------------------------------------------------------
  // - INPUT_XBAR_INPUTS:
  //     Number of input crossbar input ports
  // - INPUT_XBAR_OUTPUTS:
  //      Number of input crossbar output ports
  // - INPUT_XBAR_BITS
  //     Bitwidth of data bits in input xbar input/output packets.
  // - INPUT_XBAR_CONTROL_BITS:
  //     Bitwidth of input crossbr control bits.

  localparam int INPUT_XBAR_INPUTS = 4;
  localparam int INPUT_XBAR_OUTPUTS = 4;
  localparam int INPUT_XBAR_BITS = DATA_BITS;
  localparam int INPUT_XBAR_CONTROL_BITS = $clog2( INPUT_XBAR_INPUTS *
                                                   INPUT_XBAR_OUTPUTS );

  // Classifier Xbar ---------------------------------------------------------------
  // - CLASSIFIER_XBAR_INPUTS:
  //     Number of classifer crossbar input ports
  // - CLASSIFIER_XBAR_OUTPUTS:
  //     Number of classifer crossbar output ports
  // - CLASSIFIER_XBAR_BITS
  //     Bitwidth of data bits in classifier xbar input/output packets.
  // - CLASSIFIER_XBAR_CONTROL_BITS:
  //     Bitwidth of classifer crossbr control bits.

  localparam int CLASSIFIER_XBAR_INPUTS = 4;
  localparam int CLASSIFIER_XBAR_OUTPUTS = 4;
  localparam int CLASSIFIER_XBAR_BITS = DATA_BITS;
  localparam int CLASSIFIER_XBAR_CONTROL_BITS = $clog2( CLASSIFIER_XBAR_INPUTS *
                                                        CLASSIFIER_XBAR_OUTPUTS );

  // Output Xbar -------------------------------------------------------------------
  // - OUTPUT_XBAR_INPUTS:
  //     Number of output crossbar input ports
  // - OUTPUT_XBAR_OUTPUTS:
  //     Number of output crossbar output ports
  // - OUTPUT_XBAR_BITS
  //     Bitwidth of data bits in output xbar input/output packets.
  // - OUTPUT_XBAR_CONTROL_BITS:
  //     Bitwidth of output crossbr control bits.

  localparam int OUTPUT_XBAR_INPUTS = 3;
  localparam int OUTPUT_XBAR_OUTPUTS = 2;
  localparam int OUTPUT_XBAR_BITS = 1;
  localparam int OUTPUT_XBAR_CONTROL_BITS = $clog2( OUTPUT_XBAR_INPUTS *
                                                    OUTPUT_XBAR_OUTPUTS );

  // FFT Core 1 Deserializer -------------------------------------------------------
  // FFT Core 1 Serializer ---------------------------------------------------------
  // FFT Core 1 --------------------------------------------------------------------
  // - FFT1_SAMPLES
  //     Number of samples from FFT 1.
  // - FFT1_DECIMAL_PT
  //     Number of bits dedicated to fractional component for FFT1.
  localparam int FFT1_SAMPLES = 32;
  localparam int FFT1_DECIMAL_PT = 8;


  // FFT Core 2 Deserializer -------------------------------------------------------
  // FFT Core 2 Serializer ---------------------------------------------------------
  // FFT Core 2 --------------------------------------------------------------------
  // - FFT2_SAMPLES
  //     Number of samples from FFT 2.
  // - FFT2_DECIMAL_PT
  //     Number of bits dedicated to fractional component for FFT2.
  localparam int FFT2_SAMPLES = 32;
  localparam int FFT2_DECIMAL_PT = 8;

  // Classifier Deserializer -------------------------------------------------------
  // Classifier --------------------------------------------------------------------
  // - CLASSIFIER_SAMPLES:
  //     Number of samples by the classifier. Both FFTs generate 32 samples. FFT is
  //     conjugate symmetric. Therefore, we only need to read 32/2 samples.
  // - CLASSIFIER_BITS:
  //     Number of classifier input bits.
  // - CLASSIFIER_DECIMAL_PT:
  //     Number of classifier input bits dedicated to fractional portion.
  localparam int CLASSIFIER_SAMPLES = 16;
  localparam int CLASSIFIER_BITS = 16;
  localparam int CLASSIFIER_DECIMAL_PT = 8;

  // Wishbone Harness --------------------------------------------------------------







  //================================ASSERTS=========================================
  // SPI Minion --------------------------------------------------------------------
  // Router ------------------------------------------------------------------------
  // Arbiter -----------------------------------------------------------------------
  // Input Xbar --------------------------------------------------------------------
  generate
    if (INPUT_XBAR_CONTROL_BITS > DATA_BITS) begin
      $error("INPUT_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

  // Classifier Xbar ---------------------------------------------------------------
  generate
    if (CLASSIFIER_XBAR_CONTROL_BITS > DATA_BITS) begin
      $error("CLASSIFIER_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

  // Output Xbar -------------------------------------------------------------------
  generate
    if (OUTPUT_XBAR_CONTROL_BITS > DATA_BITS) begin
      $error("OUTPUT_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

  // FFT Core 1 Deserializer -------------------------------------------------------
  // FFT Core 1 Serializer ---------------------------------------------------------
  // FFT Core 1 --------------------------------------------------------------------
  // FFT Core 2 Deserializer -------------------------------------------------------
  // FFT Core 2 Serializer ---------------------------------------------------------
  // FFT Core 2 --------------------------------------------------------------------
  // Classifier Deserializer -------------------------------------------------------
  // Classifier --------------------------------------------------------------------
  // Wishbone Harness --------------------------------------------------------------







  //===================================WIRES========================================

  // SPI Minion --------------------------------------------------------------------
  logic [ADDR_BITS+DATA_BITS-1:0]          spi_recv_msg;
  logic                                    spi_recv_rdy;
  logic                                    spi_recv_val;
  logic [ADDR_BITS+DATA_BITS-1:0]          spi_send_msg;
  logic                                    spi_send_rdy;
  logic                                    spi_send_val;

  // Router ------------------------------------------------------------------------
  logic [ROUTER_PACKET_BITS - 1:0]         router_msg  [ROUTER_SIZE];
  logic                                    router_rdy  [ROUTER_SIZE];
  logic                                    router_val  [ROUTER_SIZE];

  // Arbiter -----------------------------------------------------------------------
  logic [ARBITER_PACKET_BITS-1:0]          arbiter_msg [ARBITER_SIZE];
  logic                                    arbiter_rdy [ARBITER_SIZE];
  logic                                    arbiter_val [ARBITER_SIZE];

  // Input Xbar --------------------------------------------------------------------
  logic [INPUT_XBAR_BITS-1:0]              input_xbar_recv_msg [INPUT_XBAR_INPUTS];
  logic                                    input_xbar_recv_rdy [INPUT_XBAR_INPUTS];
  logic                                    input_xbar_recv_val [INPUT_XBAR_INPUTS];

  logic [INPUT_XBAR_BITS-1:0]              input_xbar_send_msg [INPUT_XBAR_OUTPUTS];
  logic                                    input_xbar_send_rdy [INPUT_XBAR_OUTPUTS];
  logic                                    input_xbar_send_val [INPUT_XBAR_OUTPUTS];

  logic [INPUT_XBAR_CONTROL_BITS-1:0]      input_xbar_control_msg;
  logic                                    input_xbar_control_rdy;
  logic                                    input_xbar_control_val;

  // Classifier Xbar ---------------------------------------------------------------
  logic [CLASSIFIER_XBAR_BITS-1:0]         classifier_xbar_recv_msg [CLASSIFIER_XBAR_INPUTS];
  logic                                    classifier_xbar_recv_val [CLASSIFIER_XBAR_INPUTS];
  logic                                    classifier_xbar_recv_rdy [CLASSIFIER_XBAR_INPUTS];

  logic [CLASSIFIER_XBAR_BITS-1:0]         classifier_xbar_send_msg [CLASSIFIER_XBAR_OUTPUTS];
  logic                                    classifier_xbar_send_val [CLASSIFIER_XBAR_OUTPUTS];
  logic                                    classifier_xbar_send_rdy [CLASSIFIER_XBAR_OUTPUTS];

  logic [CLASSIFIER_XBAR_CONTROL_BITS-1:0] classifier_xbar_control_msg;
  logic                                    classifier_xbar_control_rdy;
  logic                                    classifier_xbar_control_val;

  // Output Xbar -------------------------------------------------------------------
  logic                                    output_xbar_recv_msg [OUTPUT_XBAR_INPUTS];
  logic                                    output_xbar_recv_rdy [OUTPUT_XBAR_INPUTS];
  logic                                    output_xbar_recv_val [OUTPUT_XBAR_INPUTS];

  logic                                    output_xbar_send_msg [OUTPUT_XBAR_OUTPUTS];
  logic                                    output_xbar_send_rdy [OUTPUT_XBAR_OUTPUTS];
  logic                                    output_xbar_send_val [OUTPUT_XBAR_OUTPUTS];

  logic [OUTPUT_XBAR_CONTROL_BITS-1:0]     output_xbar_control_msg;
  logic                                    output_xbar_control_rdy;
  logic                                    output_xbar_control_val;


  // FFT Core 1 Deserializer -------------------------------------------------------
  // FFT Core 1 Serializer ---------------------------------------------------------
  // FFT Core 1 --------------------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft1_recv_msg [FFT1_SAMPLES];
  logic                                    fft1_recv_val;
  logic                                    fft1_recv_rdy;
  logic [DATA_BITS-1:0]                    fft1_send_msg [FFT1_SAMPLES];
  logic                                    fft1_send_val;
  logic                                    fft1_send_rdy;


  // FFT Core 2 Deserializer -------------------------------------------------------
  // FFT Core 2 Serializer ---------------------------------------------------------
  // FFT Core 2 --------------------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft2_recv_msg [FFT2_SAMPLES];
  logic                                    fft2_recv_val;
  logic                                    fft2_recv_rdy;
  logic [DATA_BITS-1:0]                    fft2_send_msg [FFT2_SAMPLES];
  logic                                    fft2_send_val;
  logic                                    fft2_send_rdy;

  // Classifier Deserializer -------------------------------------------------------
  // Classifier --------------------------------------------------------------------
  logic [DATA_BITS-1:0]                    classifier_recv_msg [CLASSIFIER_SAMPLES];
  logic                                    classifier_recv_val;
  logic                                    classifier_recv_rdy;
  logic [DATA_BITS-1:0]                    classifier_config_msg [3];
  logic                                    classifier_config_rdy [3];
  logic                                    classifier_config_val [3];

  // Wishbone Harness --------------------------------------------------------------
  logic [31:0]                             wishbone_ostream_data [3];
  logic                                    wishbone_ostream_val  [3];
  logic                                    wishbone_ostream_rdy  [3];

  logic [31:0]                             wishbone_istream_data [3];
  logic                                    wishbone_istream_val  [3];
  logic                                    wishbone_istream_rdy  [3];







  //================================INTERCONNECT====================================
  // SPI Minion --------------------------------------------------------------------
  spi_Minion #(
    .BIT_WIDTH               (SPI_PACKET_BITS),
    .N_SAMPLES               (1)
  ) minion (
    .clk                     (clk),
    .reset                   (reset),
    .cs                      (cs),
    .mosi                    (mosi),
    .miso                    (miso),
    .sclk                    (sclk),
    .recv_msg                (spi_recv_msg),
    .recv_rdy                (spi_recv_rdy),
    .recv_val                (spi_recv_val),
    .send_msg                (spi_send_msg),
    .send_rdy                (spi_send_rdy),
    .send_val                (spi_send_val),
    .minion_parity           (minion_parity),
    .adapter_parity          (adapter_parity)
  );

  // Router ------------------------------------------------------------------------
  arbiter_router_Router #(
    .nbits                   (ROUTER_PACKET_BITS),
    .noutputs                (ROUTER_SIZE)
  ) router (
    .clk                     (clk),
    .reset                   (reset),
    .istream_val             (spi_send_val),
    .istream_msg             (spi_send_msg),
    .istream_rdy             (spi_send_rdy),
    .ostream_val             (router_val),
    .ostream_msg             (router_msg),
    .ostream_rdy             (router_rdy)
  );

  // Arbiter -----------------------------------------------------------------------
  arbiter_router_Arbiter #(
    .nbits                   (ARBITER_PACKET_BITS),
    .ninputs                 (ARBITER_SIZE)
  ) arbiter (
    .clk                     (clk),
    .reset                   (reset),
    .istream_val             (arbiter_val),
    .istream_msg             (arbiter_msg),
    .istream_rdy             (arbiter_rdy),
    .ostream_val             (spi_recv_val),
    .ostream_msg             (spi_recv_msg),
    .ostream_rdy             (spi_recv_rdy)
  );

  // Input Xbar --------------------------------------------------------------------
  // 4 inputs:
  // - Wishbone
  // - LFSR
  // - ADC
  // - Router
  // 4 outputs:
  // - Wishbone
  // - FFT 1
  // - FFT 2
  // - Arbiter (loopback)
  crossbars_Blocking #(
    .BIT_WIDTH               (INPUT_XBAR_BITS),
    .N_INPUTS                (INPUT_XBAR_INPUTS),
    .N_OUTPUTS               (INPUT_XBAR_OUTPUTS)
  ) input_xbar (
    .clk                     (clk),
    .reset                   (reset),
    .recv_msg                (input_xbar_recv_msg),
    .recv_val                (input_xbar_recv_val),
    .recv_rdy                (input_xbar_recv_rdy),
    .send_msg                (input_xbar_send_msg),
    .send_val                (input_xbar_send_val),
    .send_rdy                (input_xbar_send_rdy),
    .control                 (input_xbar_control_msg),
    .control_rdy             (input_xbar_control_rdy),
    .control_val             (input_xbar_control_val)
  );

  // Classifier Xbar ---------------------------------------------------------------
  // 4 inputs:
  // - Wishbone
  // - FFT 1
  // - FFT 2
  // - Router
  // 4 outputs:
  // - Wishbone
  // - MISR
  // - CLASSIFIER
  // - Arbiter
  crossbars_Blocking #(
    .BIT_WIDTH               (CLASSIFIER_XBAR_BITS),
    .N_INPUTS                (CLASSIFIER_XBAR_INPUTS),
    .N_OUTPUTS               (CLASSIFIER_XBAR_OUTPUTS)
  ) classifier_xbar (
    .clk                     (clk),
    .reset                   (reset),
    .recv_msg                (classifier_xbar_recv_msg),
    .recv_val                (classifier_xbar_recv_val),
    .recv_rdy                (classifier_xbar_recv_rdy),
    .send_msg                (classifier_xbar_send_msg),
    .send_val                (classifier_xbar_send_val),
    .send_rdy                (classifier_xbar_send_rdy),
    .control                 (classifier_xbar_control_msg),
    .control_rdy             (classifier_xbar_control_rdy),
    .control_val             (classifier_xbar_control_val)
  );

  // Output Xbar -------------------------------------------------------------------
  // 3 inputs:
  // - Wishbone
  // - Classifer
  // - Router
  // 2 outputs:
  // - Wishbone
  // - Arbiter
  crossbars_Blocking #(
    .BIT_WIDTH               (OUTPUT_XBAR_BITS),
    .N_INPUTS                (OUTPUT_XBAR_INPUTS),
    .N_OUTPUTS               (OUTPUT_XBAR_OUTPUTS)
  ) output_xbar (
    .clk                     (clk),
    .reset                   (reset),
    .recv_msg                (output_xbar_recv_msg),
    .recv_val                (output_xbar_recv_val),
    .recv_rdy                (output_xbar_recv_rdy),
    .send_msg                (output_xbar_send_msg),
    .send_val                (output_xbar_send_val),
    .send_rdy                (output_xbar_send_rdy),
    .control({
      output_xbar_control_msg[3:2], output_xbar_control_msg[0]
    }),  // here, we discard the second bit (index 1) as there are only 2 outputs
    .control_rdy             (output_xbar_control_rdy),
    .control_val             (output_xbar_control_val)
  );

  wire output_xbar_control_unused = &{1'b0, output_xbar_control_msg[1], 1'b0};


  // FFT Core 1 Deserializer -------------------------------------------------------
  serdes_Deserializer #(
    .N_SAMPLES               (FFT1_SAMPLES),
    .BIT_WIDTH               (DATA_BITS)
  ) fft1_deserializer (
    .clk                     (clk),
    .reset                   (reset),

    // TODO: Change. Assign these to wires explictely labeling SRC_DEST
    .recv_val                (input_xbar_send_val[2]),
    .recv_rdy                (input_xbar_send_rdy[2]),
    .recv_msg                (input_xbar_send_msg[2]),
    .send_val                (fft1_recv_val),
    .send_rdy                (fft1_recv_rdy),
    .send_msg                (fft1_recv_msg)
  );

  // FFT Core 1 Serializer ---------------------------------------------------------
  // FFT1_SAMPLES is halved here as the upper half of the result of the FFT is just
  // the complex conjugate of the lower half.
  serdes_Serializer #(
    .N_SAMPLES               (FFT1_SAMPLES/2),
    .BIT_WIDTH               (DATA_BITS)
  ) fft1_serializer (
    .clk                     (clk),
    .reset                   (reset),

    // TODO: Change. Assign these to wires explictely labeling SRC_DEST
    .send_val                (classifier_xbar_recv_val[2]),
    .send_rdy                (classifier_xbar_recv_rdy[2]),
    .send_msg                (classifier_xbar_recv_msg[2]),
    .recv_val                (fft1_send_val),
    .recv_rdy                (fft1_send_rdy),
    .recv_msg                (fft1_send_msg[0:15])
  );

  // TODO: Update bounds w/ parameters
  generate
    for (genvar i = 16; i < 32; i = i + 1) begin
      wire fft1_msg_unused = &{1'b0, fft1_send_msg[i], 1'b0};
    end
  endgenerate

  // FFT Core 1 --------------------------------------------------------------------
  fft_pease_FFT #(
    .BIT_WIDTH               (DATA_BITS),
    .DECIMAL_PT              (FFT1_DECIMAL_PT),
    .N_SAMPLES               (FFT1_SAMPLES)
  ) fft1 (
    .reset                   (reset),
    .clk                     (clk),
    .recv_msg                (fft1_recv_msg),
    .recv_val                (fft1_recv_val),
    .recv_rdy                (fft1_recv_rdy),
    .send_msg                (fft1_send_msg),
    .send_val                (fft1_send_val),
    .send_rdy                (fft1_send_rdy)
  );


  // FFT Core 2 Deserializer -------------------------------------------------------

  serdes_Deserializer #(
    .N_SAMPLES               (FFT2_SAMPLES),
    .BIT_WIDTH               (DATA_BITS)
  ) fft2_deserializer (
    .clk                     (clk),
    .reset                   (reset),

    // TODO: Change. Assign these to wires explictely labeling SRC_DEST
    .recv_val                (input_xbar_send_val[2]),
    .recv_rdy                (input_xbar_send_rdy[2]),
    .recv_msg                (input_xbar_send_msg[2]),
    .send_val                (fft2_recv_val),
    .send_rdy                (fft2_recv_rdy),
    .send_msg                (fft2_recv_msg)
  );

  // FFT Core 2 Serializer ---------------------------------------------------------
  serdes_Serializer #(
    .N_SAMPLES               (FFT2_SAMPLES/2),
    .BIT_WIDTH               (DATA_BITS)
  ) fft2_serializer (
    .clk                     (clk),
    .reset                   (reset),

    // TODO: Change. Assign these to wires explictely labeling SRC_DEST
    .send_val                (classifier_xbar_recv_val[2]),
    .send_rdy                (classifier_xbar_recv_rdy[2]),
    .send_msg                (classifier_xbar_recv_msg[2]),
    .recv_val                (fft2_send_val),
    .recv_rdy                (fft2_send_rdy),
    .recv_msg                (fft2_send_msg[0:15])
  );

  // TODO: Update bounds w/ parameters
  generate
    for (genvar i = 16; i < 32; i = i + 1) begin
      wire fft2_msg_unused = &{1'b0, fft2_send_msg[i], 1'b0};
    end
  endgenerate

  // FFT Core 2 --------------------------------------------------------------------
  fft_pease_FFT #(
    .BIT_WIDTH               (DATA_BITS),
    .DECIMAL_PT              (FFT2_DECIMAL_PT),
    .N_SAMPLES               (FFT2_SAMPLES)
  ) fft1 (
    .reset                   (reset),
    .clk                     (clk),
    .recv_msg                (fft2_recv_msg),
    .recv_val                (fft2_recv_val),
    .recv_rdy                (fft2_recv_rdy),
    .send_msg                (fft2_send_msg),
    .send_val                (fft2_send_val),
    .send_rdy                (fft2_send_rdy)
  );

  // Classifier Deserializer -------------------------------------------------------
  serdes_Deserializer #(
    .N_SAMPLES               (CLASSIFIER_SAMPLES),
    .BIT_WIDTH               (DATA_BITS)
  )classifier_deserializer(
    .clk                     (clk),
    .reset                   (reset),

    // TODO: Change. Assign these to wires explictely labeling SRC_DEST
    .recv_val                (classifier_xbar_send_val[2]),
    .recv_rdy                (classifier_xbar_send_rdy[2]),
    .recv_msg                (classifier_xbar_send_msg[2]),
    .send_val                (classifier_recv_val),
    .send_rdy                (classifier_recv_rdy),
    .send_msg                (classifier_recv_msg)
  );

  // Classifier --------------------------------------------------------------------
  classifier_Classifier #(
    .BIT_WIDTH               (CLASSIFIER_BITS),
    .DECIMAL_PT              (CLASSIFIER_DECIMAL_PT),
    .N_SAMPLES               (CLASSIFIER_SAMPLES)
  ) classifier (
    .clk                     (clk),
    .reset                   (reset),
    .recv_rdy                (classifier_recv_rdy),
    .recv_val                (classifier_recv_val),
    .recv_msg                (classifier_recv_msg),
    .cutoff_freq_rdy         (classifier_config_rdy[0]),
    .cutoff_freq_val         (classifier_config_val[0]),
    .cutoff_freq_msg         (classifier_config_msg[0]),
    .cutoff_mag_rdy          (classifier_config_rdy[1]),
    .cutoff_mag_val          (classifier_config_val[1]),
    .cutoff_mag_msg          (classifier_config_msg[1]),
    .sampling_freq_rdy       (classifier_config_rdy[2]),
    .sampling_freq_val       (classifier_config_val[2]),
    .sampling_freq_msg       (classifier_config_msg[2]),
    // hooked up to input 1 of the output
    .send_rdy                (output_xbar_recv_rdy[2]),
    .send_val                (output_xbar_recv_val[2]),
    .send_msg                (output_xbar_recv_msg[2])
  );

  // Wishbone Harness --------------------------------------------------------------
  // TODO: Params?
  wishbone_Wishbone #(
    .p_num_msgs              (3),
    .p_num_istream           (3),
    .p_num_ostream           (3)
  ) wishbone (
    .clk                     (clk),
    .reset                   (reset),
    .wbs_stb_i               (wbs_stb_i),
    .wbs_cyc_i               (wbs_cyc_i),
    .wbs_we_i                (wbs_we_i),
    .wbs_sel_i               (wbs_sel_i),
    .wbs_dat_i               (wbs_dat_i),
    .wbs_adr_i               (wbs_adr_i),
    .wbs_ack_o               (wbs_ack_o),
    .wbs_dat_o               (wbs_dat_o),
    .istream_rdy             (wishbone_istream_rdy),
    .istream_val             (wishbone_istream_val),
    .ostream_rdy             (wishbone_ostream_rdy),
    .ostream_val             (wishbone_ostream_val),
    .ostream_data            (wishbone_ostream_data),
    .istream_data            (wishbone_istream_data)
  );




  //============================================================================
  // Interconnect
  //============================================================================

  // From SPI Minion
  logic [SPI_PACKET_BITS-1:0]               SPIMinion_to_Router_msg;
  logic                                     SPIMinion_to_Router_val;
  logic                                     SPIMinion_to_Router_rdy;


  // From Router
  logic                                     Router_to_LBISTController_msg;
  logic                                     Router_to_LBISTController_val;
  logic                                     Router_to_LBISTController_rdy;

  logic [INPUT_XBAR_PACKET_BITS-1:0]        Router_to_InputXbar_msg;
  logic                                     Router_to_InputXbar_val;
  logic                                     Router_to_InputXbar_rdy;

  logic [INPUT_XBAR_CONTROL_BITS-1:0]       Router_to_InputXbarCtrl_msg;
  logic                                     Router_to_InputXbarCtrl_val;
  logic                                     Router_to_InputXbarCtrl_rdy;

  logic [CLASSIFIER_XBAR_PACKET_BITS-1:0]   Router_to_ClassifierXbar_msg;
  logic                                     Router_to_ClassifierXbar_val;
  logic                                     Router_to_ClassifierXbar_rdy;


  logic [CLASSIFIER_XBAR_CONTROL_BITS-1:0]  Router_to_ClassifierXbarCtrl; // CLASSIFIER_XBAR_CONTROL_BITS bits
  logic                                     Router_to_Classifier;         // TODO: What is bitwidth?
  logic [OUTPUT_XBAR_BITS-1:0]              Router_to_OutputXbar;         // OUTPUT_XBAR_BITS
  logic [OUTPUT_XBAR_CONTROL_BITS-1:0]      Router_to_OutputXbarCtrl;     // OUTPUT_XBAR_CONTROL_BITS bits

  assign Router_to_LBISTController_msg = router_msg[0][0];
  assign Router_to_LBISTController_val = router_val[0][0];
  assign Router_to_LBISTController_rdy = router_rdy[0][0];

  assign Router_to_InputXbar = router_msg[1][INPUT_XBAR_PACKET_BITS-1:0];
  assign Router_to_InputXbarCtrl = router_msg[2][INPUT_XBAR_CONTROL_BITS-1:0];
  assign Router_to_ClassifierXbar = router_msg[3][CLASSIFIER_XBAR_BITS-1:0];
  assign Router_to_ClassifierXbarCtrl = router_msg[4][CLASSIFIER_XBAR_CONTROL_BITS-1:0];

  // TODO: Classifier wire apparently has three connections for three things...
  assign Router_to_Classifier = 

  // From Input Xbar
  logic [INPUT_XBAR_PACKET_BITS-1:0]        InputXbar_to_Wishbone;        // INPUT_XBAR_PACKET_BITS bits
  logic [INPUT_XBAR_PACKET_BITS-1:0]        InputXbar_to_FFT1;            // INPUT_XBAR_PACKET_BITS bits
  logic [INPUT_XBAR_PACKET_BITS-1:0]        InputXbar_to_FFT2;            // INPUT_XBAR_PACKET_BITS bits
  logic [INPUT_XBAR_PACKET_BITS-1:0]        InputXbar_to_Arbiter;         // INPUT_XBAR_PACKET_BITS bits

  // From FFT1 Deserializer
  logic [DATA_BITS-1:0]                     FFT1Deserializer_to_FFT1 [FFT1_SAMPLES];

  // From FFT1
  logic [DATA_BITS-1:0]                     FFT1_to_Serializer [FFT1_SAMPLES];

  // From FFT1 Serializer
  logic [CLASSIFIER_XBAR_BITS-1:0]          FFT1Serializer_to_ClassifierXbar;

  // From FFT2 Deserializer
  logic [DATA_BITS-1:0]                     FFT2Deserializer_to_FFT2 [FFT2_SAMPLES];

  // From FFT2
  logic [DATA_BITS-1:0]                     FFT2_to_Serializer [FFT2_SAMPLES];

  // From FFT2 Serializer
  logic [CLASSIFIER_XBAR_BITS-1:0]          FFT2Serializer_to_ClassifierXbar;

  // From Classifier Xbar
  logic [CLASSIFIER_XBAR_BITS-1:0]          ClassifierXbar_to_Wishbone;
  logic [CLASSIFIER_XBAR_BITS-1:0]          ClassifierXbar_to_MISR;
  logic [CLASSIFIER_XBAR_BITS-1:0]          ClassifierXbar_to_Classifier;
  logic [CLASSIFIER_XBAR_BITS-1:0]          ClassifierXbar_to_Arbiter;

  // From Classifier
  logic                                     Classifier_to_OutputXbar;  //TODO: Check

  // From OutputXbar
  logic                                     OutputXbar_to_Wishbone;
  logic                                     OutputXbar_to_Arbiter;

  // From MISR
  logic                                     MISR_to_LBISTController; // TODO: Check
  // From Arbiter
  logic [ARBITER_PACKET_BITS-1:0]           Arbiter_to_SPIMinion;






  // 3 WB inputs:
  // 0: input xbar inject
  assign input_xbar_recv_msg[1] = wishbone_istream_data[0][DATA_BITS-1:0];
  assign input_xbar_recv_val[1] = wishbone_istream_val[0];
  assign wishbone_istream_rdy[0] = input_xbar_recv_rdy[1];
  // 1: classifier xbar inject
  assign classifier_xbar_recv_msg[1] = wishbone_istream_data[1][DATA_BITS-1:0];
  assign classifier_xbar_recv_val[1] = wishbone_istream_val[1];
  assign wishbone_istream_rdy[1] = classifier_xbar_recv_rdy[1];
  // 2: output xbar inject
  assign output_xbar_recv_msg[1] = wishbone_istream_data[2][0];
  assign output_xbar_recv_val[1] = wishbone_istream_val[2];
  assign wishbone_istream_rdy[2] = output_xbar_recv_rdy[1];

  wire unused_wishbone_istream_bits = &{
    1'b0,
    wishbone_istream_data[0][31:DATA_BITS],
    wishbone_istream_data[1][31:DATA_BITS],
    wishbone_istream_data[2][31:1],
    1'b0
  };

  // 3 WB outputs:
  // 0: input xbar output
  // sign extend the 16 bit data to 32 bits
  assign wishbone_ostream_data[0] = {
    {(32 - DATA_BITS) {input_xbar_send_msg[1][DATA_BITS-1]}}, input_xbar_send_msg[1]
  };
  assign wishbone_ostream_val[0] = input_xbar_send_val[1];
  assign input_xbar_send_rdy[1] = wishbone_ostream_rdy[0];
  // 1: classifier xbar output
  assign wishbone_ostream_data[1] = {
    {(32 - DATA_BITS) {classifier_xbar_send_msg[1][DATA_BITS-1]}}, classifier_xbar_send_msg[1]
  };
  assign wishbone_ostream_val[1] = classifier_xbar_send_val[1];
  assign classifier_xbar_send_rdy[1] = wishbone_ostream_rdy[1];
  // 2: output xbar output
  // zero extend the classifier output to 32 bits
  assign wishbone_ostream_data[2] = {31'b0, output_xbar_send_msg[1]};
  assign wishbone_ostream_val[2] = output_xbar_send_val[1];
  assign output_xbar_send_rdy[1] = wishbone_ostream_rdy[2];

  // 9 inputs:
  // 0: input xbar inject
  assign input_xbar_recv_msg[0] = router_msg[0][DATA_BITS-1:0];
  assign input_xbar_recv_val[0] = router_val[0];
  assign router_rdy[0] = input_xbar_recv_rdy[0];
  // 1: input xbar config
  assign input_xbar_control_msg = router_msg[1][XBAR_CTRL_BITS-1:0];
  assign input_xbar_control_val = router_val[1];
  assign router_rdy[1] = input_xbar_control_rdy;
  // 2: classifier xbar inject
  assign classifier_xbar_recv_msg[0] = router_msg[2][DATA_BITS-1:0];
  assign classifier_xbar_recv_val[0] = router_val[2];
  assign router_rdy[2] = classifier_xbar_recv_rdy[0];
  // 3: classifier xbar config
  assign classifier_xbar_control_msg = router_msg[3][XBAR_CTRL_BITS-1:0];
  assign classifier_xbar_control_val = router_val[3];
  assign router_rdy[3] = classifier_xbar_control_rdy;
  // 4: output xbar inject
  // 1 bit here as the classifier output is 1 bit wide
  assign output_xbar_recv_msg[0] = router_msg[4][0];
  assign output_xbar_recv_val[0] = router_val[4];
  assign router_rdy[4] = output_xbar_recv_rdy[0];
  // 5: output xbar config
  assign output_xbar_control_msg = router_msg[5][XBAR_CTRL_BITS-1:0];
  assign output_xbar_control_val = router_val[5];
  assign router_rdy[5] = output_xbar_control_rdy;
  // 6: classifier cutoff freq
  assign classifier_config_msg[0] = router_msg[6][DATA_BITS-1:0];
  assign classifier_config_val[0] = router_val[6];
  assign router_rdy[6] = classifier_config_rdy[0];
  // 7: classifier cutoff mag
  assign classifier_config_msg[1] = router_msg[7][DATA_BITS-1:0];
  assign classifier_config_val[1] = router_val[7];
  assign router_rdy[7] = classifier_config_rdy[1];
  // 8: classifier sampling freq
  assign classifier_config_msg[2] = router_msg[8][DATA_BITS-1:0];
  assign classifier_config_val[2] = router_val[8];
  assign router_rdy[8] = classifier_config_rdy[2];
  // 9: loopback to arbiter
  assign arbiter_msg[9] = router_msg[9][DATA_BITS-1:0];
  assign arbiter_val[9] = router_val[9];
  assign router_rdy[9] = arbiter_rdy[9];
  // 10+: unused
  generate
    for (genvar i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin
      assign router_rdy[i] = 1'b0;
    end
  endgenerate

  // config messages for the classifiers shorter than 16 bits
  wire unused_xbar_cfg_bits = &{
    1'b0,
    router_msg[1][DATA_BITS-1:XBAR_CTRL_BITS],
    router_msg[3][DATA_BITS-1:XBAR_CTRL_BITS],
    router_msg[5][DATA_BITS-1:XBAR_CTRL_BITS],
    1'b0
  };
  // output xbar inject is 1 bit wide
  wire unused_output_xbar_msg = &{1'b0, router_msg[4][DATA_BITS-1:1], 1'b0};
  // address bits are retained by the router but we don't use them
  generate
    for (genvar i = 0; i <= 9; i = i + 1) begin
      wire unused_router_addr = &{1'b0, router_msg[i][DATA_BITS+ADDR_BITS-1:DATA_BITS], 1'b0};
    end
  endgenerate
  wire unused_router_val = &{1'b0, router_val[10:ROUTER_ARBITER_SIZE-1], 1'b0};
  wire unused_router_msg = &{1'b0, router_msg[10:ROUTER_ARBITER_SIZE-1], 1'b0};

  // 5 outputs:
  // 0: input xbar output
  assign arbiter_msg[0] = input_xbar_send_msg[0];
  assign arbiter_val[0] = input_xbar_send_val[0];
  assign input_xbar_send_rdy[0] = arbiter_rdy[0];
  // 1: unused
  assign arbiter_msg[1] = 16'b0;
  assign arbiter_val[1] = 1'b0;

  // 2: classifier xbar output
  assign arbiter_msg[2] = classifier_xbar_send_msg[0];
  assign arbiter_val[2] = classifier_xbar_send_val[0];
  assign classifier_xbar_send_rdy[0] = arbiter_rdy[2];
  // 3: unused
  assign arbiter_msg[3] = 16'b0;
  assign arbiter_val[3] = 1'b0;

  // 4: output xbar output
  // zero extend the classifier output to 16 bits
  assign arbiter_msg[4] = {15'b0, output_xbar_send_msg[0]};
  assign arbiter_val[4] = output_xbar_send_val[0];
  assign output_xbar_send_rdy[0] = arbiter_rdy[4];
  // 5-8: unused
  generate
    for (genvar i = 5; i <= 8; i = i + 1) begin
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

  // 9: loopback to arbiter
  // 10+: unused
  generate
    for (genvar i = 10; i < ROUTER_ARBITER_SIZE; i = i + 1) begin
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

  wire unused_arbiter_rdy = &{
    1'b0,
    arbiter_rdy[1],
    arbiter_rdy[3],
    arbiter_rdy[5:8],
    arbiter_rdy[10:ROUTER_ARBITER_SIZE-1],
    1'b0
  };

endmodule

`endif