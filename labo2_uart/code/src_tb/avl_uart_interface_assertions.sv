module avl_uart_interface_assertions #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
) (
    input logic avl_clk_i,
    input logic avl_reset_i,

    input logic [13:0] avl_address_i,
    input logic [ 3:0] avl_byteenable_i,
    input logic [31:0] avl_readdata_o,
    input logic [31:0] avl_writedata_i,
    input logic        avl_write_i,
    input logic        avl_read_i,
    input logic        avl_waitrequest_o,
    input logic        avl_readdatavalid_o,
    input logic        rx_i,
    input logic        tx_o
);

  // clocking block
  default clocking cb @(posedge avl_clk_i);
  endclocking

  // read and write shall never be active at the same time
  assume_readwrite :
  assume property (!(avl_write_i & avl_read_i));

  // En lecture, la donnée est prête un cycle après que avl_read_i est à ’1’.
  // En lecture, avl_readdatavalid_o s’active lorsque la donnée est disponible.
  assume_readdatavalid_after_read :
  assume property (avl_read_i |=> avl_readdatavalid_o);

  //Le signal byteenable n’est pas utilisé.
  assume_byteenable_is_not_used :
  assume property (avl_byteenable_i == 8'hf);

  //En écriture, avl_waitrequest_o permet de faire patienter le master, selon le fonction-
  //nement normal du bus avalon.
  assume_wait_request_is_respected :
  assume property (avl_waitrequest_o && avl_write_i |=> avl_write_i && (avl_writedata_i == $past(
      avl_writedata_i
  )));

  // Vérifie que le status du buffer tx est cohérent
  // i.e le status vide et le status plein ne sont pas les deux à 1
  assume_status_register_tx_fifo_status_coherence :
  assume property (avl_read_i && (avl_address_i == 0)
    |=> (avl_readdata_o[3] == 0 || (avl_readdata_o[3] != avl_readdata_o[0])));


  // Vérifie que le status du buffer rx est cohérent
  // i.e si le buffer est plein, il faut aussi que le registre indique un
  // élément disponible
  assume_status_register_rx_fifo_status_coherence :
  assume property (avl_read_i && (avl_address_i == 0) ##1 avl_readdata_o[1] |-> avl_readdata_o[2]);

  // vérifie que la ligne tx_o repasse `eventuellement` à 1
  assume_tx_eventually_goes_back_to_1 :
  assume property ($fell(tx_o) |=> ##[0:$] tx_o == 1);

  // vérifie que la ligne rx_i repasse `eventuellement` à 1
  assume_rx_eventually_goes_back_to_1 :
  assume property ($fell(rx_i) |=> ##[0:$] rx_i == 1);

  //Valide qu'on n'essaie pas de lire une adresse plus grande que 3
  assume_address_on_read_is_lower_than_4 :
  assume property (avl_read_i |-> (avl_address_i < 4));

  //Valide qu'on n'essaie pas d'écrire une adresse plus grande que 3
  assume_address_on_write_is_lower_than_4 :
  assume property (avl_write_i |-> avl_address_i < 4);

  //Valide que la valeur qui sort du DUV n'est jamais plus grande que la
  //valeur max
  //Ceci présume aussi que la donnée est prête le coup de clock d'après du
  //read -> Ceci est dit sur la donnée
  assume_read_data_is_not_bigger_than_datasize :
  assume property (avl_readdata_o && (avl_address_i == 2) |=> avl_readdata_o < 2 ** DATASIZE);


endmodule
