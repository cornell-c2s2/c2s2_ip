// =================================================================================
// Author: Johnny Martinez
// Date: 02/16/2025
// Documentation: https://confluence.cornell.edu/display/c2s2/Tapein1+-+Goose
//
// Spec:
// PARAMETERS ----------------------------------------------------------------------
// I/O -----------------------------------------------------------------------------
// =================================================================================

`ifndef TAPEIN1_SP25_TOP_V
`define TAPEIN1_SP25_TOP_V

`include "spi/minion.v"
`include "arbiter_router/router.v"
`include "arbiter_router/arbiter.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"
`include "crossbars/blocking.v"
`include "classifier/classifier.v"
`include "lbist/lbist_controller/lbist_controller.v"
`include "lbist/lfsr/lfsr_galois.v"
`include "lbist/misr/misr.v"
`include "cmn/reset_sync.v"
`include "async_fifo/AsyncFifo.sv"
`include "async_fifo/FifoPackager.sv"


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
  output logic  adapter_parity
);

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
  //  ------------------------------------------------------------------------------
  // | ADDRESS       |                             DATA                             |
  //  ------------------------------------------------------------------------------
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

  localparam int OUTPUT_XBAR_INPUTS = 4;
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

  // LBIST Controller --------------------------------------------------------------
  // - SEED_BITS:
  //     Number of bits for each seed; number of bits for each test vector generated by
  //     the LFSR.
  // - SIGNATURE_BITS:
  //     Number of bits for each hash/signature generated by the MISR.
  // - NUM_SEEDS:
  //     Number of seeds to iterate over (not the number of test
  //     vectors generated per seed).
  // - NUM_HASHES:
  //     The number of outputs from the CUT the MISR should hash into a unique
  //     signature/hash.
  // - MAX_OUTPUTS_TO_HASH:
  //     The max number of outputs from the CUT the MISR can hash. Note,
  //     MAX_OUTPUTS_TO_HASH >= NUM_HASHES
  // - LFSR_SEEDS
  //     An array of seeds to be sent to the LFSR.
  // - EXPECTED_SIGNATURES:
  //     The expected signature values from CUT to be compared against result of
  //     MISR
  localparam int SEED_BITS = DATA_BITS;
  localparam int SIGNATURE_BITS = DATA_BITS;
  localparam int NUM_SEEDS = 8;
  localparam int NUM_HASHES = 80;
  localparam int MAX_OUTPUTS_TO_HASH = 100;
  localparam [SEED_BITS-1:0] LFSR_SEEDS [NUM_SEEDS-1:0] = {
    32'b10101110100101100000101111000010,
    32'b10000111001110100111100001011100,
    32'b10001111101000100111111010010111,
    32'b10111010000110110000000000110111,
    32'b11010011001001101011100100010101,
    32'b01100101110011011100001001101000,
    32'b10100011101101000101010111100011,
    32'b11011100011010111001110000101001
  };
  localparam [SIGNATURE_BITS-1:0] EXPECTED_SIGNATURES [NUM_SEEDS-1:0] = {
      16'b1100111001111011,
      16'b1100101001001101,
      16'b1001011011010011,
      16'b0100110110111010,
      16'b1010110001010011,
      16'b1101000101011111,
      16'b1101010001100010,
      16'b1000111010101101
  };

  // LFSR --------------------------------------------------------------------------
  // MISR --------------------------------------------------------------------------
  // - MISR_SEED:
  //     Seed used by MISR to create signatures.
  // - MISR_MSG_BITS:
  //     Bitwidth of MISR signatures.
  localparam int MISR_SEED = '0;
  localparam int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH);

  // Async FIFO --------------------------------------------------------------------
  // - FIFO_DEPTH:
  //     Number of FIFO Entries.
  // - FIFO_ENTRY_BITS:
  //     Bitwidth of each FIFO Entry
  localparam int FIFO_DEPTH = 10;
  localparam int FIFO_ENTRY_BITS = 8;

  // FIFO Packager -----------------------------------------------------------------
  // - PACKAGER_BITS:
  //     Bitwidth of each packager input message
  // - PACKAGER_CONCAT:
  //     Number of valid inputs for the packager to concatanate
  localparam int PACKAGER_BITS = FIFO_ENTRY_BITS;
  localparam int PACKAGER_CONCAT = 2;




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

  logic [INPUT_XBAR_BITS-1:0]       Router_to_InputXbar_msg;
  logic                                    Router_to_InputXbar_val;
  logic                                    Router_to_InputXbar_rdy;

  logic [CLASSIFIER_XBAR_BITS-1:0]         Router_to_ClassifierXbar_msg;
  logic                                    Router_to_ClassifierXbar_val;
  logic                                    Router_to_ClassifierXbar_rdy;

  logic [OUTPUT_XBAR_BITS-1:0]             Router_to_OutputXbar_msg;
  logic                                    Router_to_OutputXbar_rdy;
  logic                                    Router_to_OutputXbar_val;

  logic [ARBITER_PACKET_BITS-1:0]          Router_to_Arbiter_msg;
  logic                                    Router_to_Arbiter_val;
  logic                                    Router_to_Arbiter_rdy;

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

  logic [ARBITER_PACKET_BITS-1:0]          InputXbar_to_Arbiter_msg;
  logic                                    InputXbar_to_Arbiter_val;
  logic                                    InputXbar_to_Arbiter_rdy;

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

  logic [ARBITER_PACKET_BITS-1:0]          ClassifierXbar_to_Arbiter_msg;
  logic                                    ClassifierXbar_to_Arbiter_val;
  logic                                    ClassifierXbar_to_Arbiter_rdy;

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

  logic  [ARBITER_PACKET_BITS-1:0]         OutputXbar_to_Arbiter_msg;
  logic                                    OutputXbar_to_Arbiter_val;
  logic                                    OutputXbar_to_Arbiter_rdy;

  // FFT Core 1 Deserializer -------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft1_deserializer_recv_msg;
  logic                                    fft1_deserializer_recv_val;
  logic                                    fft1_deserializer_recv_rdy;

  // FFT Core 1 Serializer ---------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft1_serializer_send_msg;
  logic                                    fft1_serializer_send_val;
  logic                                    fft1_serializer_send_rdy;

  // FFT Core 1 --------------------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft1_recv_msg [FFT1_SAMPLES];
  logic                                    fft1_recv_val;
  logic                                    fft1_recv_rdy;
  logic [DATA_BITS-1:0]                    fft1_send_msg [FFT1_SAMPLES];
  logic                                    fft1_send_val;
  logic                                    fft1_send_rdy;

  // FFT Core 2 Deserializer -------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft2_deserializer_recv_msg;
  logic                                    fft2_deserializer_recv_val;
  logic                                    fft2_deserializer_recv_rdy;

  // FFT Core 2 Serializer ---------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft2_serializer_send_msg;
  logic                                    fft2_serializer_send_val;
  logic                                    fft2_serializer_send_rdy;

  // FFT Core 2 --------------------------------------------------------------------
  logic [DATA_BITS-1:0]                    fft2_recv_msg [FFT2_SAMPLES];
  logic                                    fft2_recv_val;
  logic                                    fft2_recv_rdy;
  logic [DATA_BITS-1:0]                    fft2_send_msg [FFT2_SAMPLES];
  logic                                    fft2_send_val;
  logic                                    fft2_send_rdy;

  // Classifier Deserializer -------------------------------------------------------
  logic [DATA_BITS-1:0]                    classifier_deserializer_recv_msg;
  logic                                    classifier_deserializer_recv_val;
  logic                                    classifier_deserializer_recv_rdy;

  // Classifier --------------------------------------------------------------------
  logic [DATA_BITS-1:0]                    classifier_recv_msg [CLASSIFIER_SAMPLES];
  logic                                    classifier_recv_val;
  logic                                    classifier_recv_rdy;
  logic [DATA_BITS-1:0]                    classifier_config_msg [3];
  logic                                    classifier_config_rdy [3];
  logic                                    classifier_config_val [3];
  logic                                    classifier_send_msg;
  logic                                    classifier_send_val;
  logic                                    classifier_send_rdy;

  // LBIST Controller --------------------------------------------------------------
  logic                                    lbist_req_val;
  logic                                    lbist_req_rdy;

  logic                                    lbist_resp_val;
  logic [NUM_SEEDS-1:0]                    lbist_resp_msg;
  logic                                    lbist_resp_rdy;

  logic                                    ctrl_lfsr_resp_val;
  logic [SEED_BITS-1:0]                    ctrl_lfsr_resp_msg;
  logic                                    ctrl_lfsr_resp_rdy;

  logic                                    ctrl_misr_req_val;
  logic [MISR_MSG_BITS:0]                  ctrl_misr_req_msg;
  logic                                    ctrl_misr_req_rdy;

  logic                                    lfsr_cut_reset;

  // LFSR --------------------------------------------------------------------------
  logic                                    lfsr_resp_val;
  logic [SEED_BITS-1:0]                    lfsr_resp_msg;
  logic                                    lfsr_resp_rdy;
  // MISR --------------------------------------------------------------------------
  logic                                    cut_misr_resp_val;
  logic [SIGNATURE_BITS-1:0]               cut_misr_resp_msg;
  logic                                    cut_misr_resp_rdy;

  logic                                    misr_resp_val;
  logic [SIGNATURE_BITS-1:0]               misr_resp_msg;
  logic                                    misr_resp_rdy;

  // Async FIFO --------------------------------------------------------------------
  logic [FIFO_ENTRY_BITS-1:0]              async_fifo_recv_msg;
  logic                                    async_fifo_recv_val;
  logic                                    async_fifo_recv_rdy;

  logic [FIFO_ENTRY_BITS-1:0]              async_fifo_send_msg;
  logic                                    async_fifo_send_val;
  logic                                    async_fifo_send_rdy;

  // FIFO Packager -----------------------------------------------------------------
  logic [DATA_BITS-1:0]                    packager_send_msg;
  logic                                    packager_send_val;
  logic                                    packager_send_rdy;







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
    .control                 (output_xbar_control_msg),
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
    .recv_val                (fft1_deserializer_recv_val),
    .recv_rdy                (fft1_deserializer_recv_rdy),
    .recv_msg                (fft1_deserializer_recv_msg),
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
    .send_val                (fft1_serializer_send_val),
    .send_rdy                (fft1_serializer_send_rdy),
    .send_msg                (fft1_serializer_send_msg),
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
    .recv_val                (fft2_deserializer_recv_val),
    .recv_rdy                (fft2_deserializer_recv_rdy),
    .recv_msg                (fft2_deserializer_recv_msg),
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
    .send_val                (fft2_serializer_send_val),
    .send_rdy                (fft2_serializer_send_rdy),
    .send_msg                (fft2_serializer_send_msg),
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
  ) fft2 (
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
    .recv_val                (classifier_deserializer_recv_val),
    .recv_rdy                (classifier_deserializer_recv_rdy),
    .recv_msg                (classifier_deserializer_recv_msg),
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
    .send_rdy                (classifier_send_rdy),
    .send_val                (classifier_send_val),
    .send_msg                (classifier_send_msg)
  );

  // LBIST Controller --------------------------------------------------------------
  lbist_controller #(
    .SEED_BITS               (SEED_BITS),
    .SIGNATURE_BITS          (SIGNATURE_BITS),
    .NUM_SEEDS               (NUM_SEEDS),
    .NUM_HASHES              (NUM_HASHES),
    .MAX_OUTPUTS_TO_HASH     (MAX_OUTPUTS_TO_HASH),
    .MISR_MSG_BITS           (MISR_MSG_BITS),
    .LFSR_SEEDS              (LFSR_SEEDS),
    .EXPECTED_SIGNATURES     (EXPECTED_SIGNATURES)
  ) lbist_controller (
    .clk                     (clk),
    .reset                   (reset),
    .lbist_req_val           (lbist_req_val),
    .lbist_req_rdy           (lbist_req_rdy),
    .lbist_resp_val          (lbist_resp_val),
    .lbist_resp_msg          (lbist_resp_msg),
    .lbist_resp_rdy          (lbist_resp_rdy),
    .lfsr_resp_val           (ctrl_lfsr_resp_val),
    .lfsr_resp_msg           (ctrl_lfsr_resp_msg),
    .lfsr_resp_rdy           (ctrl_lfsr_resp_rdy),
    .lfsr_cut_reset          (lfsr_cut_reset),
    .misr_req_val            (ctrl_misr_req_val),
    .misr_req_msg            (ctrl_misr_req_msg),
    .misr_req_rdy            (ctrl_misr_req_rdy),
    .misr_resp_val           (misr_resp_val),
    .misr_resp_msg           (misr_resp_msg),
    .misr_resp_rdy           (misr_resp_rdy)
  );

  // LFSR --------------------------------------------------------------------------
  lfsr_galois #(
    .LFSR_MSG_BITS           (SEED_BITS)
  ) lfsr (
    .clk                     (clk),
    // TODO: Ensure FFTs and their serializers also gets this reset...
    .reset                   (reset || lfsr_cut_reset),
    .req_val                 (ctrl_lfsr_resp_val),
    .req_msg                 (ctrl_lfsr_resp_msg),
    .req_rdy                 (ctrl_lfsr_resp_rdy),
    .resp_rdy                (lfsr_resp_rdy),
    .resp_val                (lfsr_resp_val),
    .resp_msg                (lfsr_resp_msg)
  );

  // MISR --------------------------------------------------------------------------
  misr #(
    .CUT_MSG_BITS            (SIGNATURE_BITS),
    .SIGNATURE_BITS          (SIGNATURE_BITS),
    .MAX_OUTPUTS_TO_HASH     (MAX_OUTPUTS_TO_HASH),
    .LBIST_MSG_BITS          (MISR_MSG_BITS),
    .SEED                    (MISR_SEED)
  ) misr (
    .clk                     (clk),
    .reset                   (reset),
    .cut_req_val             (cut_misr_resp_val),
    .cut_req_msg             (cut_misr_resp_msg),
    .cut_req_rdy             (cut_misr_resp_rdy),
    .lbist_req_val           (ctrl_misr_req_val),
    .lbist_req_msg           (ctrl_misr_req_msg),
    .lbist_req_rdy           (ctrl_misr_req_rdy),
    .lbist_resp_val          (misr_resp_val),
    .lbist_resp_msg          (misr_resp_msg),
    .lbist_resp_rdy          (misr_resp_rdy)
  );

  // Async FIFO --------------------------------------------------------------------
  AsyncFifo #(
    .p_num_entries           (FIFO_DEPTH),
    .p_bit_width             (FIFO_ENTRY_BITS)
  ) async_fifo (
    .i_clk(),
    .o_clk                   (clk),
    .async_rst               (reset),
    .istream_msg             (async_fifo_recv_msg),
    .istream_val             (async_fifo_recv_val),
    .istream_rdy             (async_fifo_recv_rdy),
    .ostream_msg             (async_fifo_send_msg),
    .ostream_val             (async_fifo_send_val),
    .ostream_rdy             (async_fifo_send_rdy)
  );


  // TODO: Update w/ actual values
  assign async_fifo_recv_msg = '0;
  assign async_fifo_recv_val = 1'b0;

  // FIFO Packager -----------------------------------------------------------------
  FifoPackager #(
    .p_bit_width             (PACKAGER_BITS),
    .p_num_concat            (PACKAGER_CONCAT)
  ) packager (
    .clk                     (clk),
    .reset                   (reset),
    .req_msg                 (async_fifo_send_msg),
    .req_val                 (async_fifo_send_val),
    .req_rdy                 (async_fifo_send_rdy),
    .resp_msg                (packager_send_msg),
    .resp_val                (packager_send_val),
    .resp_rdy                (packager_send_rdy)
  );



  //===============================ROUTING_LOGIC====================================
  // Router ------------------------------------------------------------------------
  // Addressing Scheme:
  // ** Router has 4 address bits. This corresponds to 16 output ports.**
  // 0000 - LBIST Controller
  // 0001 - Input XBar
  // 0010 - Input XBar Ctrl
  // 0011 - Classifier Xbar
  // 0100 - Classifier Xbar Ctrl
  // 0101 - Classifier Cutoff Frequency Ctrl
  // 0110 - Classifier Cutoff Magnetude Ctrl
  // 0111 - Classifier Sampling Frequency Ctrl
  // 1000 - Output Xbar
  // 1001 - Output Xbar Ctrl
  // 1010 - Arbiter (Loopback)
  // 1011 - Unused
  // 1100 - Unused
  // 1101 - Unused
  // 1110 - Unused
  // 1111 - Unused

  // Address: 0000 - LBIST Controller
  assign lbist_req_val = router_val[0];
  assign router_rdy[0] = lbist_req_rdy;

  // Address: 0001 - Input XBar
  assign Router_to_InputXbar_msg = router_msg[1][ROUTER_PACKET_BITS-1:0];
  assign Router_to_InputXbar_val = router_val[1];
  assign router_rdy[1] = Router_to_InputXbar_rdy;

  // Address: 0010 - Input XBar Ctrl
  assign input_xbar_control_msg = router_msg[2][INPUT_XBAR_CONTROL_BITS-1:0];
  assign input_xbar_control_val = router_val[2];
  assign router_rdy[2] = input_xbar_control_rdy;

  // Address: 0011 - Classifier Xbar
  assign Router_to_ClassifierXbar_msg = router_msg[3][ROUTER_PACKET_BITS-1:0];
  assign Router_to_ClassifierXbar_val = router_val[3];
  assign router_rdy[3] = Router_to_Arbiter_rdy;

  // Address: 0100 - Classifier Xbar Ctrl
  assign classifier_xbar_control_msg = router_msg[4][CLASSIFIER_XBAR_CONTROL_BITS-1:0];
  assign classifier_xbar_control_val = router_val[4];
  assign router_rdy[4] = classifier_xbar_control_rdy;

  // Address: 0101 - Classifier Cutoff Frequency Ctrl
  assign classifier_config_msg[0] = router_msg[5][DATA_BITS-1:0];
  assign classifier_config_val[0] = router_val[5];
  assign router_rdy[5] = classifier_config_rdy[0];

  // Address: 0110 - Classifier Cutoff Magnetude Ctrl
  assign classifier_config_msg[1] = router_msg[6][DATA_BITS-1:0];
  assign classifier_config_val[1] = router_val[6];
  assign router_rdy[6] = classifier_config_rdy[1];

  // Address: 0111 - Classifier Sampling Frequency Ctrl
  assign classifier_config_msg[2] = router_msg[7][DATA_BITS-1:0];
  assign classifier_config_val[2] = router_val[7];
  assign router_rdy[7] = classifier_config_rdy[2];

  // Address: 1000 - Output Xbar
  assign Router_to_OutputXbar_msg = router_msg[8][OUTPUT_XBAR_BITS];
  assign Router_to_OutputXbar_val = router_val[8];
  assign router_rdy[8] = Router_to_OutputXbar_rdy;

  // Address: 1001 - Output Xbar Ctrl
  assign output_xbar_control_msg = router_msg[9][OUTPUT_XBAR_CONTROL_BITS-1:0];
  assign output_xbar_control_val = router_val[9];
  assign router_rdy[9] = output_xbar_control_rdy;

  // Address: 1010 - Arbiter (Loopback)
  assign Router_to_Arbiter_msg = router_msg[10][ARBITER_PACKET_BITS-1:0];
  assign Router_to_Arbiter_val = router_val[10];
  assign router_rdy[10] = Router_to_Arbiter_rdy;

  // Address 11 onwards are unused!
  generate
    for (genvar i = 11; i < ROUTER_SIZE; i = i + 1) begin
      assign router_rdy[i] = 1'b0;
    end
  endgenerate


  // Input Xbar --------------------------------------------------------------------
  // Addressing Scheme:
  // **Input Xbar has 4 input ports and 4 output ports.**
  // Inputs:
  // 00 - LFSR
  // 01 - FIFO Packager
  // 10 - Router
  // Outputs:
  // 00 - FFT1 Deserializer
  // 01 - FFT2 Deserializer
  // 10 - Arbiter

  // Input port: 00 - LFSR
  assign input_xbar_recv_msg[0] = lfsr_resp_msg;
  assign input_xbar_recv_val[0] = lfsr_resp_val;
  assign lfsr_resp_rdy = input_xbar_recv_rdy[0];

  // Input port: 01 - FIFO Packager
  // Each fifo output is 8 bits
  assign input_xbar_recv_msg[1] = packager_send_msg;
  assign input_xbar_recv_val[1] = packager_send_val;
  assign packager_send_rdy = input_xbar_recv_rdy[1];

  // Input port: 10 - Router
  assign input_xbar_recv_msg[2] = Router_to_InputXbar_msg;
  assign input_xbar_recv_val[2] = Router_to_InputXbar_val;
  assign Router_to_InputXbar_rdy = input_xbar_recv_rdy[2];


  // Output port: 00 - FFT1 Deserializer
  assign fft1_deserializer_recv_msg = input_xbar_send_msg[0];
  assign fft1_deserializer_recv_val = input_xbar_send_val[0];
  assign input_xbar_send_rdy[0] = fft1_deserializer_recv_rdy;

  // Output port: 01 - FFT2 Deserializer
  assign fft2_deserializer_recv_msg = input_xbar_send_msg[1];
  assign fft2_deserializer_recv_val = input_xbar_send_val[1];
  assign input_xbar_send_rdy[1] = fft2_deserializer_recv_rdy;

  // Output port: 10 - Arbiter
  assign InputXbar_to_Arbiter_msg = input_xbar_send_msg[2];
  assign InputXbar_to_Arbiter_val = input_xbar_send_val[2];
  assign input_xbar_send_rdy[2] = InputXbar_to_Arbiter_rdy;


  // Classifier Xbar ---------------------------------------------------------------
  // Addressing Scheme:
  // **Classifier Xbar has 4 input ports and 4 output ports.**
  // Inputs:
  // 00 - FFT1 Serializer
  // 01 - FFT2 Serializer 
  // 10 - Router 
  // Outputs:
  // 00 - MISR
  // 01 - Classifier Deserializer
  // 10 - Arbiter

  // Input port: 00 - FFT1 Serializer
  assign classifier_xbar_recv_msg[0] = fft1_serializer_send_msg;
  assign classifier_xbar_recv_val[0] = fft1_serializer_send_val;
  assign fft1_serializer_send_rdy = classifier_xbar_recv_rdy[0];

  // Input port: 01 - FFT2 Serializer
  assign classifier_xbar_recv_msg[1] = fft2_serializer_send_msg;
  assign classifier_xbar_recv_val[1] = fft2_serializer_send_val;
  assign fft2_serializer_send_rdy = classifier_xbar_recv_rdy[1];

  // Input port: 10 - Router
  assign classifier_xbar_recv_msg[2] = Router_to_ClassifierXbar_msg;
  assign classifier_xbar_recv_val[2] = Router_to_ClassifierXbar_val;
  assign Router_to_ClassifierXbar_rdy = classifier_xbar_recv_rdy[2];


  // Output port: 00 - MISR
  assign cut_misr_resp_msg = classifier_xbar_send_msg[0];
  assign cut_misr_resp_val = classifier_xbar_send_val[0];
  assign classifier_xbar_send_rdy[0] = cut_misr_resp_rdy;

  // Output port: 01 - Classifier Deserializer
  assign classifier_deserializer_recv_msg = classifier_xbar_send_msg[1];
  assign classifier_deserializer_recv_val = classifier_xbar_send_val[1];
  assign classifier_xbar_send_rdy[1] = classifier_deserializer_recv_rdy;

  // Output port: 10 - Arbiter
  assign ClassifierXbar_to_Arbiter_msg = classifier_xbar_send_msg[2];
  assign ClassifierXbar_to_Arbiter_val = classifier_xbar_send_val[2];
  assign classifier_xbar_send_rdy[2] = ClassifierXbar_to_Arbiter_rdy;


  // Output Xbar -------------------------------------------------------------------
  // Addressing Scheme:
  // **Output Xbar has 4 input ports and 2 output ports.**
  // Inputs:
  // 00 - Classifier
  // 01 - Router
  // 10 - Unused
  // Outputs:
  // 0 - Arbiter

  // Input port: 00 - Classifier
  assign output_xbar_recv_msg[0] = classifier_send_msg;
  assign output_xbar_recv_val[0] = classifier_send_val;
  assign classifier_send_rdy = output_xbar_recv_rdy[0];

  // Input port: 01 - Router
  assign output_xbar_recv_msg[1] = Router_to_OutputXbar_msg;
  assign output_xbar_recv_val[1] = Router_to_OutputXbar_val;
  assign Router_to_OutputXbar_rdy = output_xbar_recv_rdy[1];

  // Input port: 10 - Unused
  assign output_xbar_recv_msg[2] = '0;
  assign output_xbar_recv_val[2] = '0;


  // Output Port: 1 - Arbiter
  assign OutputXbar_to_Arbiter_msg = {15'b0, output_xbar_send_msg[0]};
  assign OutputXbar_to_Arbiter_val = output_xbar_send_val[0];
  assign output_xbar_send_rdy[0] = OutputXbar_to_Arbiter_rdy;

  // Arbiter -----------------------------------------------------------------------
  // Addressing Scheme:
  // **Arbiter has 16 ports. Arbiter appends address bits to selected packet. LSB prioritized**
  // Docs: https://confluence.cornell.edu/display/c2s2/Arbiter
  // Outputs (highest priority)
  // 0 - Router (loopback)
  // 1 - Input Xbar
  // 2 - Classifier Xbar
  // 3 - Output Xbar
  // 4 - LBIST Controller
  // 5 - Unused
  // 6 - Unused
  // 7 - Unused
  // 8 - Unused
  // 9 - Unused
  // 10 - Unused
  // 11 - Unused
  // 12 - Unused
  // 13 - Unused
  // 14 - Unused
  // 15 - Unused
  // (lowest priority)

  // Port 0: Router (loopback)
  assign arbiter_msg[0] = Router_to_Arbiter_msg;
  assign arbiter_val[0] = Router_to_Arbiter_val;
  assign Router_to_Arbiter_rdy = arbiter_rdy[0];

  // Port 1: Input Xbar
  assign arbiter_msg[1] = InputXbar_to_Arbiter_msg;
  assign arbiter_val[1] = InputXbar_to_Arbiter_val;
  assign InputXbar_to_Arbiter_rdy = arbiter_rdy[1];

  // Port 2: Classifier Xbar
  assign arbiter_msg[2] = ClassifierXbar_to_Arbiter_msg;
  assign arbiter_val[2] = ClassifierXbar_to_Arbiter_val;
  assign ClassifierXbar_to_Arbiter_rdy = arbiter_rdy[2];

  // Port 3: Output Xbar
  assign arbiter_msg[3] = OutputXbar_to_Arbiter_msg;
  assign arbiter_val[3] = OutputXbar_to_Arbiter_val;
  assign OutputXbar_to_Arbiter_rdy = arbiter_rdy[3];

  // Port 4: LBIST Controller
  assign arbiter_msg[4] = lbist_resp_msg;
  assign arbiter_val[4] = lbist_resp_val;
  assign lbist_resp_rdy = arbiter_rdy[4];

  // Unused ports
  generate
    for (genvar i = 5; i < ARBITER_SIZE; i = i + 1) begin
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

  // wire unused_arbiter_rdy = &{
  //   1'b0,
  //   arbiter_rdy[4:ARBITER_SIZE-1],
  //   1'b0
  // };


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
  // LBIST Controller --------------------------------------------------------------
  // LFSR --------------------------------------------------------------------------
  // MISR --------------------------------------------------------------------------
  // Async FIFO --------------------------------------------------------------------
  // FIFO Packager -----------------------------------------------------------------



endmodule

`endif
