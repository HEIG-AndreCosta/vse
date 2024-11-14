Vérification formelle adapté pour des petites systèmes simples avec des cas d'utilisation relativement limités.

## Utilisation d'un loggeur

Pour pouvoir facilement modifier les messages qui sont affichés (selon le niveau de gravité), pouvoir facilement définir un fichier de sortie, le type du fichier de sortie etc..

## Compteur

Relativement limité en cas d'utilisation, on peut facilement décrire le comportement attendu et donc utiliser la verification formelle pour le vérifier.

## Design complexe

Mélanger la vérification formelle et fonctionnelle. Il est rapidement difficile de mettre en place la vérification formelle.

![alt text](image-2.png)

```sv
coverpoint rssi;
cov_size_low : coverpoint size {
        bins low[16] = {[0:15]};
        ignore_bins others = default;
}
cov_adv: coverpoint adv;

cross cov_size_low, cov_adv;

cov_channel: coverpoint channel {
        bins b1 = {0};
        bins b2 = {24};
        bins b3 = {78};
        ignore_bins others = default;
}
cov_adv_one : coverpoint adv {
    bins b1 = {1};
    ignore_bins others = default;
}

cross cov_adv_one, cov_channel;

coverpoint address {
  option.auto_bin_max = 255;
}
```

![alt text](image-3.png)

```sv
default clocking cb @(posedge clk);
endclocking

assert property (!(a & b));
assert property  (valid |=> busy && !acq ##[1:$] !busy && acq);
assert property (wr |-> active );
assert property (wr[*2] |-> $stable(address) & $stable(data));
assert property ($fell(wr) |-> $past(ready));
```

![alt text](image-4.png)

```sv
class Packet;
...
rand bit wrong_parity;
rand bit mult_four;

constraint wp_distr {
    wrong_parity dist {
        0 := 99,
        1 := 1
    }
}
constraint mfour_dist {
    mult_four dist {
        0 := 75,
        1 := 25
    }
}

function post_randomize();
    parity = calc_parity(data,length);
    if (wrong_parity) begin
        parity = ~parity
    end
endfunction

constraint type {
    (ptype == 0) -> (length == 0);

    (ptype != 0 && mult_four) -> (length % 4 == 0);

    (ptype != 0 && !mult_four) -> (length % 4 != 0);
}

constraint source_dst {
    source != dest;
}
constraint dst {
    (ptype == 1) -> (dest > source);
}

constraint order {
    solve ptype before length, source, dest;
    solve mult_four before length;
}

```

![alt text](image-5.png)
