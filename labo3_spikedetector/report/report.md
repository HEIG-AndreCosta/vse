<img src="logo.png" style="height:80px;">

# <center> Laboratoire n°03 {ignore=true}

# <center> Détection de spike - Traitement de signal {ignore=true}

## <center>Département : TIC {ignore=true}

## <center>Unité d’enseignement VSE {ignore=true}

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Auteur: **Andrè Costa & Alexandre Iorio**

Professeur: **Yann Thoma**

Assistant : **-**

Salle de labo : **A07**

Date : **13.12.2024**

<!--pagebreak-->

## <center>Table des matières {ignore=true}

<!-- @import "[TOC]" {cmd="toc" depthFrom=1 depthTo=6 orderedList=false} -->

<!-- code_chunk_output -->

- [1. Introduction](#1-introduction)
- [2. Déroulement](#2-déroulement)
  - [2.1. Refactorisation](#21-refactorisation)
  - [2.2. Plusieurs activations des acquisitions](#22-plusieurs-activations-des-acquisitions)
  - [2.3. Tests unitaires](#23-tests-unitaires)
    - [2.3.1. Spike Detector](#231-spike-detector)
    - [2.3.2. FpgaAccessRemote](#232-fpgaaccessremote)
  - [2.4 Définition du fichier de simulation](#24-définition-du-fichier-de-simulation)
  - [2.5 Génération des fichiers de simulation](#25-génération-des-fichiers-de-simulation)
  - [2.6 Finalisation de la simulation](#26-finalisation-de-la-simulation)
  - [2.7 Définition du Port](#27-définition-du-port)
  - [2.8 Généralisation des tests d'intégration](#28-généralisation-des-tests-dintégration)
  - [2.9 Tests d'intégration](#29-tests-dintégration)
  - [2.10 Lancement des tests manuellement](#210-lancement-des-tests-manuellement)
    - [2.10.1 Tests unitaires](#2101-tests-unitaires)
    - [2.10.2 Tests d'intégration](#2102-tests-dintégration)
    - [2.10.3 Script pour lancer les tests](#2103-script-pour-lancer-les-tests)

<!-- /code_chunk_output -->

<!-- pagebreak -->

## 1. Introduction

## 2. Déroulement

### 2.1. Refactorisation

Comme indiqué sur l'énoncé, le code fourni a des problèmes d'architecture et de lisibilité. Nous avons donc commencé par le refactoriser.

D'un côté, la refactorisation devrait permettre de réutiliser une partie du code si on souhaite changer l'implémentation de l'accès à la FPGA. D'un autre côté, elle devrait permettre de réutiliser la partie d'accès par serveur TCP pour pouvoir tester d'autres DUVs.

Tout d'abord, nous avons abstrait le concept d'accès à une FPGA.

Nous avons créé une interface `FpgaAccess` qui est responsable de fournir les méthodes nécessaires pour s'interfacer avec une FPGA.
Notamment, des méthodes pour configurer l'accès (`setup`), lire et écrire des registres (`read/write_register`) et encore pour définir une fonction de callback pour les interruptions.

```c
typedef void (*irq_handler_t)(const std::string &);

class FpgaAccess {
  public:
    virtual void setup() = 0;
    virtual void write_register(uint16_t reg, uint16_t value) = 0;
    virtual uint16_t read_register(uint16_t reg) = 0;
    virtual void set_callback(irq_handler_t) = 0;
};
```

Nous pouvons alors imaginer une classe `SpikeDetector` qui peut se construire avec un objet implémentant cette interface.

```c
typedef void (*on_message_cb)(const std::string &);
class SpikeDetector {
  public:
    SpikeDetector(std::shared_ptr<FpgaAccess> access, on_message_cb cb);
    ~SpikeDetector() = default;

    void start_acquisition();
    void stop_acquisition();
    bool is_acquisition_in_progress();
    bool is_data_ready();

    uint16_t get_status();
    uint16_t get_window_address();

    bool read_window(SpikeWindow &data);
    void set_on_new_data_callback(on_message_cb);
    void set_simulation_file(const char *path);
};
```

Cette classe nous permet de directement abstraire l'accès au DUV, on ne parle plus de registres mais de concepts comme `Acquisition`, `DataReady`, etc...

Pour compléter cette refactorisation, il manque la classe d'accès à la FPGA. La responsabilité de cette classe est de fournir les méthodes de l'interface `FpgaAccess` avec le protocole custom TCP fourni.

```c
struct SetupOptions {
  bool wait_for_connection;
  uint16_t port;
};

class FpgaAccessRemote : public FpgaAccess {
  public:
    FpgaAccessRemote(SetupOptions opts);
    ~FpgaAccessRemote();

    void setup();
    void write_register(uint16_t reg, uint16_t value);
    uint16_t read_register(uint16_t reg);
    void set_callback(irq_handler_t);
    void set_simulation_file(const char *path);
}
```

Ceci nous permet d'écrire du code comme:

```c
// main
detector.start_acquisition();

// spike_detector
void SpikeDetector::start_acquisition()
{
  access->write_register(1, 1);
}

// fpga_access_remote
void FpgaAccessRemote::write_register(uint16_t reg, uint16_t value)
{
  std::stringstream stream;
  stream << "wr " << reg << " " << value << std::endl;
  this->do_send(stream.str());
}
```

Ce qui peut être caractérisé comme très élégant si j'ose dire.

<!-- pagebreak -->

### 2.2. Plusieurs activations des acquisitions

Comme indiqué dans l'énoncé, l'implémentation du côté SystemVerilog ne permet pas d'arrêter et de redémarrer les acquisitions.

Pour résoudre ce problème, tout d'abord il faut detécter la demande d'arrêt de l'acquisition.

```verilog
task avalon_write(int address, int data);
 ...
  if (address == 1) begin
    if (data == 0) begin
      $display("%t Stopping acquisition", $time);
      is_active = 0;
    end else if (data == 1) begin
      $display("%t Starting acquisition", $time);
      is_active = 1;
      ->start_record;
    end
  end
```

Ici nous mettons tout simplement un flag `is_active` à 0 pour arrêter l'acquisition. Dans la tâche qui envoi des données, il peut alors vérifier ce flag à chaque cycle pour savoir s'il doit continuer ou non.

```verilog
while (!$feof(
    fd
)) begin
  ret = $fscanf(fd, "%d", val);
  if (!is_active) begin
    $display("%t Acquisition Stopped. Waiting...", $time);
    wait (start_record.triggered);
    $display("%t Acquisition Restarted", $time);
  end
  ...
end
```

Ensuite on peut juste attendre à nouveau que l'événement `start_record` soit déclenché pour continuer l'acquisition.

Les tests du côté software seront démontrés plus tard dans ce rapport.

### 2.3. Tests unitaires

Avec la décomposition mise en place au niveau software, il est très simple de mettre en place des tests unitaires.

#### 2.3.1. Spike Detector

Pour pouvoir construire un objet du type `SpikeDetector` il faut lui fournir un objet implémentant l'interface `FpgaAccess`. Pour les tests unitaires, on peut alors créer un objet `MockFpgaAccess` qui implémente cette interface.

```c
struct Access {
  bool is_read;
  int reg;
  int value;
};
struct Register {
  uint16_t address;
  uint16_t value;
};

class MockFpgaAccess : public FpgaAccess {
  public:
    MockFpgaAccess(const std::vector<Register> &registers);
    ~MockFpgaAccess() = default;

    void setup();
    void write_register(uint16_t reg, uint16_t value);

    uint16_t read_register(uint16_t reg);
    void set_callback(irq_handler_t);

    void set_simulation_file(const char *path);
    std::vector<Access> access;
    const std::vector<Register> &registers;
    const char *file_set;
    bool setup_called;
    irq_handler_t handler;
};
```

Les structures `Access` et `Register` sont utilisées pour stocker les accès aux registres et les valeurs à retourner lors de la lecture.

Les appels à `write_register` et `read_register`nt implique alors un stockage d'un `Access` avec le registre et la valeur passée en paramètre.

```c
void MockFpgaAccess::write_register(uint16_t reg, uint16_t value)
{
  access.push_back(Access{
    .is_read = false,
    .reg = reg,
    .value = value,
  });
}
```

Pour permettre bien tester la lecture de registres, un appel à `read_register` doit retourner la valeur stockée dans le vecteur `registers`.

```c
uint16_t MockFpgaAccess::read_register(uint16_t reg)
{
  for (const auto &r : registers) {
    if (r.address == reg) {
      access.push_back(Access{
        .is_read = true,
        .reg = reg,
        .value = r.value,
      });
      return r.value;
    }
  }
  return 0xFFFF;
}
```

Avec cette implémentation, on peut alors tester la classe `SpikeDetector` en vérifiant que les appels à `write_register` et `read_register` sont corrects.

L'écriture d'un test unitaire pour les méthodes `start_acquisition` et `stop_acquisition` se ressemble à ceci:

```c
TEST(TestSpikeDetector, StartStopAcquisition)
{
  // Créer notre objet MockFpgaAccess
  std::vector<Register> v;
  auto access = std::make_shared<MockFpgaAccess>(v);

  // Créer notre SpikeDetector
  SpikeDetector sd = { access, handler };

  // Appeler les fonctions à tester
  sd.start_acquisition();
  sd.stop_acquisition();

  // Vérifier que le nombre d'accès est correct
  ASSERT_EQ(access->access.size(), 2);

  // Vérifier que les types et valeurs des accès sont corrects
  ASSERT_FALSE(access->access[0].is_read);
  ASSERT_EQ(access->access[0].reg, 1);
  ASSERT_EQ(access->access[0].value, 1);

  ASSERT_FALSE(access->access[1].is_read);
  ASSERT_EQ(access->access[1].reg, 1);
  ASSERT_EQ(access->access[1].value, 0);
}
```

Comme nous avons un contrôle complet sur la classe `MockFpgaAccess` nous pouvons tout vérifier, voici les idées que nous avons eu:

1. Tester que la fonction `setup` est bien appellée
2. Tester que la fonction `set_callback` est bien appellée
3. Tester que les différentes fonctions de lecture retournent les bonnes valeurs

   - Nottament pour les fonctions `is_data_ready` et `is_acquisition_in_progress` qui demandent de masquer le bit 0 et 1 du registre `Status` respectivement.

#### 2.3.2. FpgaAccessRemote

La classe `FpgaAccessRemote` est un peu plus complexe, comme elle ouvre un serveur TCP, il faut se connecter dessus et vérifier ce qu'il se passe lorsqu'on envoie des données.

Avant de pouvoir faire cela correctement, quelques modifications à l'implémentation originale ont été nécessaires.

L'implémentation originale de cette classe ouvrait un serveur TCP et attendait la connexion d'un client avant de retourner de la fonction `setup`. Ceci est pratique pour l'application finale, on ne va pas essayer de communiquer avec la FPGA avant que le client ne soit connecté.
Pour les tests unitaires, cette implémentation nous présente le problème de l'oeuf et la poule, nous ne pouvons pas nous connecter avant que le serveur soit ouvert et la fonction ne retourne pas avant que nous nous soyons connectés.

Nous aurions pu utiliser des threads pour résoudre cela mais cela aurait été trop compliqué pour un simple test unitaire.

Le thread qui était responsable d'ouvrir le serveur et d'attendre les connexions ne fait plus qu'attendre les connexions et est démarré après l'ouverture du serveur.

```c
void FpgaAccessRemote::start_server(uint16_t port)
{
  // Code pour ouverture du serveur
  ...
  // Démarre un thread pour attendre la connexion du client
  listener_thread =
    std::thread(&FpgaAccessRemote::accept_connection, this, sockfd);
}
```

Et avec une simple variable de configuration nous pouvons décider si nous voulons attendre la connexion du client ou non.

```c
void FpgaAccessRemote::setup()
{
	start_server(opts.port);
	rx_thread = std::thread(&FpgaAccessRemote::receiver, this);

	if (opts.wait_for_connection) {
		wait_connection();
	}
}
```

Avec cette modification, nous pouvons maintenant démarrer les tests unitaires avec un bout de code du type:

```c
TEST(TestFpgaAccessRemote, ...)
{
  // On indique de ne pas attendre la connexion
  SetupOptions opts = { .wait_for_connection = false, .port = 1238 };
  FpgaAccessRemote access{ opts };

  // Cette fonction retourne après l'ouverture du serveur
  access.setup();
  // On peut désormais se connecter dessus
  int socket = connect_to_server(opts.port);
}
```

Les tests unitaires vérifient surtout le format des messages envoyés et reçus. Par exemple, pour la fonction `write_register` on vérifie que le message envoyé est bien du format `wr <reg> <value>`.

```c
TEST(TestFpgaAccessRemote, WriteRegister)
{
	SetupOptions opts = { .wait_for_connection = false, .port = 1236 };
	FpgaAccessRemote access{ opts };
	access.setup();
	int socket = connect_to_server(opts.port);

	access.write_register(1, 2);

	char msg[50];
	const char *expected = "wr 1 2\n";

	ssize_t bytes = recv(socket, msg, sizeof(msg), MSG_DONTWAIT);
	msg[bytes] = 0;

	EXPECT_EQ(bytes, strlen(expected));
	EXPECT_STREQ(msg, expected);
	close(socket);
}
```

Pour cette classe les différentes idées testés ont été:

1. `setup` ouvre bien un serveur TCP
2. `write_register` envoie bien le bon message
3. `read_register` envoie la bonne requête et retourne la bonne valeur
4. `callback` est bien appellée lors qu'un message `irq` est reçu
5. Aucun crash n'arrive si la `callback` est nulle
6. La fonction `callback` peut être modifié en cours d'exécution
7. Le message `end_test` est envoyé lors de la destruction de l'objet

### 2.4 Définition du fichier de simulation

Pour les tests d'intégration, il est intéressant de pouvoir lancer avec différents fichiers de données différents, pour être sûr que le spike detector fonctionne correctement.
Pour cela, il faut pouvoir envoyer un fichier de simulation à la FPGA.

Pour cela nous avons implémenté une commande spéciale `set_file <file>` qui permet d'envoyer un fichier de simulation à la FPGA.

Du côté SystemVerilog, nous avons ajouté un événement qui est déclénché lors de la récéption de cette commande.
Notons que cette commande est obligatoire et ne permet pas de modifier le fichier en cours de simulation. Il ne serait pas intéressant de pouvoir changer le fichier en cours de simulation, car la vérification serait très compliquée voir impossible.

```verilog
// Event
event input_file_set;

// Dans la tâche de reception des commandes
...
else if (command == "set_file") begin
  ret = $sscanf(recv_msg, "set_file %s", input_file);
  ->input_file_set;
end
...

// Au début de la tâche de lecture des données.
// Avant d'attendre le premier `start_record`
...
wait (input_file_set.triggered);
...
```

### 2.5 Génération des fichiers de simulation

Pour générer les fichiers de simulation, nous avons créé un script Python qui génère des valeurs aléatoires pour les fenêtres de données.

```python
content = "\n".join([str(i) for i in range(900)])

with open("linear.txt", "w") as f:
    f.write(content)

content = "0\n" * 900

with open("zeros.txt", "w") as f:
    f.write(content)

content = ("0\n" * 70 + "1000\n" + "0\n" * 100) * 17 + ("0\n" * 200)

with open("constant_spikes_16_windows.txt", "w") as f:
    f.write(content)
```

Ici les fenêtres sont assez petites, pour lancer des petites simulations et vérifier le comportement du DUV.

Le dernier fichier `constant_spikes_16_windows.txt` est un fichier très intéressant car il est utile pour pouvoir débougger et, en plus le nombre de fenêtres équivaut au nombre de fenêtres disponibles en mémoire par le DUV.

### 2.6 Finalisation de la simulation

Une autre amélioration effectué au système original est l'envoi d'un message Simulation -> Software pour indiquer que nous avons finalisé de jouer les données du fichier. Ceci accèlere les tests considèrablement vu que la condition d'arrêt précédente était d'attendre 5 minutes après le dernier `irq`.

Du côté SystemVerilog, la tâche qui joue les données du fichier attend un certain une quantité de coups d'horloge après avoir joué la dernière donnée et envoie un message de fin au software.
Pour pouvoir facilement ajouter ce message sans beaucoup modifier, le message démarre avec la chaîne `irq` car du côté software, tout est déjà fait pour traiter les messages qui commencent par `irq`.

```verilog
// Wait one window size clks to give the DUV
// time to produce another IRQ if needed
##150;
client.send_mbox.put("irq end\n");
$display("Simulation is over");
```

```c
// main
while (irqCondVar.wait_for(lk, std::chrono::seconds(600),
        [] { return !irqFifo.empty(); })) {
  std::string value = irqFifo.back();
  irqFifo.pop();
  if (strstr(value.c_str(), "end")) {
    break;
  }
  ...
}
```

### 2.7 Définition du Port

Même en ajoutant le mécanisme de fin de simulation, le test avec le fichier `input_values.txt` fourni au début prend environ 5 minutes à jour. Comme nous voulons accèlérer, l'idée serait de démarrer plusieurs simulations en même temps. Pour ce faire, le `port` du serveur TCP doit être configurable pour que chaque paire Simulation - Test Software puisse avoir son propre port.

Du côté server, ceci a déjà été montré. Le port est indiqué dans la structure `SetupOptions` et est utilisé pour ouvrir le serveur.

```c
struct SetupOptions {
  bool wait_for_connection;
  uint16_t port;
};
```

Du côté SystemVerilog, ceci est passé comme paramètre générique lors du lancement du programme.

Il faut donc modifier le `Makefile` et le script `arun.sh` pour pouvoir utiliser un paramètre qui sera configuré en tant que variable d'environnement.

Dans `arun.sh`, il faut que ce paramètre soit utilisé pour créer des librairies différentes pour chaque simulation

```bash
run_with_questa() {
    if [ -d work${SERVER_PORT} ]; then
        rm -rf work${SERVER_PORT}
    fi
    mkdir work${SERVER_PORT}

    cd work${SERVER_PORT}
    vlib work${SERVER_PORT}
    ...
}
```

Et dans le makefile, le paramètre doit être envoyé avec le prefixe `-G`

```makefile
run_questa: build_questa
	cd work$(SERVER_PORT); vsim -64 amiq_top -do vsim_cmds.do -lib work -GPORT=$(SERVER_PORT)

```

Et finalement, nous pouvons récuperer cette variable dans le test bench.

```verilog
module amiq_top #(
    int ERRNO = 0,
    int PORT  = 8888
);
...
  amiq_server_connector #(
      .hostname("127.0.0.1"),
      .port(PORT),
      .delim("\n")
  ) client = new();
...
```

### 2.8 Généralisation des tests d'intégration

Du côté software, le différents tests que l'on veut lancer sont très similaires et pour éviter de répéter du code, nous avons créé une fonction qui prend en paramètre les différents paramètres nécessaires pour lancer un tests.
Deux de ces paramètres sont des fonctions qui servent à définir ce que le test doit faire lorsqu'il reçoit un `irq` et une fois une lecture de fenêtre effectuée.

```c
typedef bool (*on_irq_trigger_t)(const std::queue<std::string> &,
				 SpikeDetector &);
typedef void (*on_window_read_t)(SpikeDetector &);

void test_file(const char *simulation_file, uint16_t port,
	       size_t expected_spike_nb, on_irq_trigger_t on_irq,
	       on_window_read_t on_window_read);
```

### 2.9 Tests d'intégration

Toute cette préparation nous permet maintenant de facilement tester, en parallèle, plusieurs fichiers différents.

Pour lancer un test "classique" avec le fichier `input_values.txt` il suffit de lancer la commande suivante:

```c
static bool on_irq_read_window(const std::queue<std::string> &fifo,
			       SpikeDetector &detector)
{
  (void)detector;
  // Retourne true pour indiquer au test de lire la donnée
  return true;
}
static void on_window_read_do_nothing(SpikeDetector &detector)
{
  (void)detector;
}

TEST(Integration, RandomSpikes)
{
  test_file("../../../../simulation_files/input_values.txt",
      port_from_env(), 52, on_irq_read_window,
      on_window_read_do_nothing);
}
```

Les différents idées de tests sont:

1. Les fichiers `zeros.txt` et `linear.txt` permettent de vérifier que le DUV ne détecte pas de spikes s'il n'y en a pas.

2. Le fichier `input_values.txt` permet de vérifier que le DUV détecte bien les spikes avec des valeurs qui simulent des valeurs qui peuvent s'approcher de la réalité.

3. Le fichier `constant_spikes_16_windows.txt` nous permet d'ajouter un test où l'on ne lit aucune fenêtre et vérifier que nous pouvons récupérer les données plus tard sans problème.

4. Pour finir, nous avons aussi ajouté un test où l'on arrête et redémarre l'acquisition plusieurs fois pour vérifier que le DUV fonctionne correctement.

### 2.10 Lancement des tests manuellement

#### 2.10.1 Tests unitaires

Pour les tests unitaires aller dans le répertoire `embeded_soft/test/unit`

```bash
cmake -S . -B build
cmake --build build
./build/test_spike_detector
./build/test_fpga_access_remote
```

#### 2.10.2 Tests d'intégration

1. Générer les fichiers de simulation dans le répertoire `simulation_files`

```bash
python3 generate.py
```

2. Builder les tests d'intégration souhaité dans `embeded_soft/test/integration`

```bash
cmake -S . -B build
cmake --build build
```

3. Choisir le test à lancer

```bash
./build/test_integration --gtest_list_tests
```

4. Lancer le test choisi. Par exemple pour lancer le test `Integration.RandomSpikes`

```bash
export SERVER_PORT=8888
./build/test_integration --gtest_filter=Integration.RandomSpikes
```

5. Lancer la simulation dans le répertoire `fpga_sim`

```bash
export PROJ_HOME=${PWD}
export SERVER_PORT=8888
./arun.sh -tool questa
```

Notons qu'il est possible de lancer plusieurs simulations en même temps en exportant la variable `SERVER_PORT` avec des valeurs différentes.

#### 2.10.3 Script pour lancer les tests

Un script est fourni pour lancer tous les tests en parallèle. Ceci va ouvrir plusieurs fois `questasim` donc a ne pas utiliser si votre ordinateur risque de chauffer votre pièce.

Il a été testé sous Fedora 41 et dans la VM Reds mais il est fourni sans garanties. Nottament, vérifiez que votre système est connecté sur le VPN pour avoir lancer `questasim`.

Dans le répertoire `code` lancer

```bash
python run_tests.py
```
