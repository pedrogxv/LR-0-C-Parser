#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <algorithm>
#include <stdexcept>
using namespace std;

// estrutura para representar uma producao da gramatica: A -> alfa
struct Producao {
    string lado_esquerdo;  // nao-terminal do lado esquerdo
    vector<string> lado_direito;  // simbolos do lado direito
};

// item lr(0): [A -> alfa . beta] representado por indice da producao e posicao do ponto
struct Item {
    int indice_producao;  // qual producao (indice no vetor de producoes)
    int posicao_ponto;    // posicao do ponto (0..tamanho do lado direito)
    bool operator==(Item const &outro) const { 
        return indice_producao == outro.indice_producao && posicao_ponto == outro.posicao_ponto; 
    }
};

// funcao hash para usar Item em unordered_set
struct ItemHash { 
    size_t operator()(Item const &item) const noexcept { 
        return (item.indice_producao << 16) ^ item.posicao_ponto; 
    } 
};

// estado do automato lr(0) = conjunto de items
using Estado = vector<Item>;;

// funcao auxiliar para juntar strings com separador
static string juntar_strings(const vector<string>& vetor, const string &separador=" "){
    string resultado;
    for(size_t i=0; i<vetor.size(); ++i){ 
        if(i) resultado += separador; 
        resultado += vetor[i]; 
    }
    return resultado;
}

// le arquivo da gramatica e retorna vetor de producoes
vector<Producao> ler_gramatica(const string &caminho_arquivo, set<string> &nao_terminais, set<string> &terminais){
    ifstream arquivo(caminho_arquivo);
    if(!arquivo) throw runtime_error("nao foi possivel abrir arquivo da gramatica: " + caminho_arquivo);
    
    vector<Producao> producoes;
    string linha;
    
    // funcao auxiliar para remover espacos em branco
    auto remover_espacos = [](string texto){
        size_t inicio = texto.find_first_not_of(" \t\r\n");
        if(inicio == string::npos) return string();
        size_t fim = texto.find_last_not_of(" \t\r\n");
        return texto.substr(inicio, fim - inicio + 1);
    };
    
    while(getline(arquivo, linha)){
        // remove comentarios apos #
        auto pos_comentario = linha.find('#');
        if(pos_comentario != string::npos) linha = linha.substr(0, pos_comentario);
        
        linha = remover_espacos(linha);
        if(linha.empty()) continue;
        
        // formato esperado: A -> alfa | beta
        auto pos_seta = linha.find("->");
        if(pos_seta == string::npos) 
            throw runtime_error("producao invalida (falta ->): " + linha);
        
        string lado_esq = remover_espacos(linha.substr(0, pos_seta));
        nao_terminais.insert(lado_esq);
        
        string resto = linha.substr(pos_seta + 2);
        
        // divide alternativas pelo simbolo |
        vector<string> alternativas;
        size_t inicio = 0;
        while(inicio < resto.size()){
            size_t pos_barra = resto.find('|', inicio);
            if(pos_barra == string::npos){ 
                alternativas.push_back(remover_espacos(resto.substr(inicio))); 
                break; 
            }
            alternativas.push_back(remover_espacos(resto.substr(inicio, pos_barra - inicio)));
            inicio = pos_barra + 1;
        }
        
        // cria uma producao para cada alternativa
        for(auto &alternativa: alternativas){
            Producao prod;
            prod.lado_esquerdo = lado_esq;
            
            // divide os simbolos do lado direito por espacos
            stringstream stream(alternativa);
            string simbolo;
            while(stream >> simbolo){
                if(simbolo == "eps") continue;  // epsilon (producao vazia)
                prod.lado_direito.push_back(simbolo);
            }
            producoes.push_back(prod);
        }
    }
    
    // coleta terminais: simbolos que aparecem mas nao sao nao-terminais
    for(auto &prod: producoes){
        for(auto &simbolo: prod.lado_direito) {
            if(nao_terminais.count(simbolo) == 0) 
                terminais.insert(simbolo);
        }
    }
    terminais.insert("$");  // simbolo de fim de entrada
    return producoes;
}

// retorna o simbolo apos o ponto no item, ou string vazia se ponto esta no final
string simbolo_apos_ponto(const Item &item, const vector<Producao> &producoes){
    const auto &prod = producoes[item.indice_producao];
    if(item.posicao_ponto < (int)prod.lado_direito.size()) 
        return prod.lado_direito[item.posicao_ponto];
    return string();
}

// verifica se o ponto esta no final do item (item completo)
bool ponto_no_final(const Item &item, const vector<Producao> &producoes){
    return item.posicao_ponto >= (int)producoes[item.indice_producao].lado_direito.size();
}

// calcula o fechamento (closure) de um conjunto de items
// adiciona todos os items [B -> .gama] onde B aparece apos o ponto em algum item
Estado calcular_fechamento(const Estado &conjunto_items, const vector<Producao> &producoes, 
                           const set<string> &nao_terminais){
    unordered_set<Item, ItemHash> conjunto_fechamento(conjunto_items.begin(), conjunto_items.end());
    queue<Item> fila;
    
    for(auto &item: conjunto_items) fila.push(item);
    
    while(!fila.empty()){
        Item item_atual = fila.front(); 
        fila.pop();
        
        string simbolo = simbolo_apos_ponto(item_atual, producoes);
        if(simbolo.empty()) continue;  // ponto no final
        if(nao_terminais.count(simbolo) == 0) continue;  // nao e nao-terminal
        
        // para cada producao B -> gama onde B = simbolo, adiciona [B -> .gama]
        for(int i=0; i<(int)producoes.size(); ++i){
            if(producoes[i].lado_esquerdo == simbolo){
                Item novo_item{i, 0};
                if(!conjunto_fechamento.count(novo_item)) { 
                    conjunto_fechamento.insert(novo_item); 
                    fila.push(novo_item); 
                }
            }
        }
    }
    
    Estado resultado(conjunto_fechamento.begin(), conjunto_fechamento.end());
    
    // ordena deterministicamente para comparacao de estados
    sort(resultado.begin(), resultado.end(), [](const Item &x, const Item &y){ 
        if(x.indice_producao != y.indice_producao) return x.indice_producao < y.indice_producao; 
        return x.posicao_ponto < y.posicao_ponto; 
    });
    
    return resultado;
}

// calcula goto(estado, simbolo): novo estado ao processar simbolo
// move o ponto sobre o simbolo em todos os items relevantes
Estado calcular_goto(const Estado &estado_atual, const string &simbolo, 
                     const vector<Producao> &producoes, const set<string> &nao_terminais){
    Estado novo_conjunto;
    
    for(auto &item: estado_atual){
        string simb_apos = simbolo_apos_ponto(item, producoes);
        if(!simb_apos.empty() && simb_apos == simbolo){
            // move o ponto uma posicao a frente
            novo_conjunto.push_back({item.indice_producao, item.posicao_ponto + 1});
        }
    }
    
    return calcular_fechamento(novo_conjunto, producoes, nao_terminais);
}

// busca o indice de um estado na colecao, retorna -1 se nao encontrado
int buscar_indice_estado(const vector<Estado> &colecao_estados, const Estado &estado_procurado){
    for(size_t i=0; i<colecao_estados.size(); ++i){
        if(colecao_estados[i].size() != estado_procurado.size()) continue;
        
        bool estados_iguais = true;
        for(size_t j=0; j<estado_procurado.size(); ++j) {
            if(!(colecao_estados[i][j] == estado_procurado[j])) { 
                estados_iguais = false; 
                break; 
            }
        }
        
        if(estados_iguais) return (int)i;
    }
    return -1;
}

// acao do analisador: shift, reduce, accept ou erro
struct Acao {
    enum Tipo {ERRO, SHIFT, REDUCE, ACCEPT} tipo = ERRO;
    int valor = -1;  // numero do estado (shift) ou indice da producao (reduce)
};

int main(int argc, char **argv){
    if(argc < 3){
        cerr<<"uso: "<<argv[0]<<" <arquivo-gramatica> <tokens-entrada (entre aspas, separados por espaco)>\n";
        cerr<<"exemplo: ./lr0_parser grammar.txt \"a a a\"\n";
        return 1;
    }
    
    string arquivo_gramatica = argv[1];
    string entrada_string;
    
    // junta os argumentos restantes em uma string de tokens
    for(int i=2; i<argc; ++i){ 
        if(i>2) entrada_string += " "; 
        entrada_string += argv[i]; 
    }

    set<string> nao_terminais, terminais;
    vector<Producao> producoes = ler_gramatica(arquivo_gramatica, nao_terminais, terminais);
    if(producoes.empty()) { 
        cerr<<"nenhuma producao lida\n"; 
        return 1; 
    }

    // aumenta a gramatica: S' -> S (S e o nao-terminal da primeira producao)
    string simbolo_inicial = producoes[0].lado_esquerdo;
    Producao prod_aumentada;
    prod_aumentada.lado_esquerdo = simbolo_inicial + "'";
    prod_aumentada.lado_direito = {simbolo_inicial};
    producoes.insert(producoes.begin(), prod_aumentada);
    nao_terminais.insert(prod_aumentada.lado_esquerdo);

    terminais.insert("$");

    // constroi a colecao canonica de estados lr(0)
    Estado estado_inicial;
    estado_inicial.push_back({0, 0});  // [S' -> .S]
    Estado fechamento_inicial = calcular_fechamento(estado_inicial, producoes, nao_terminais);
    
    vector<Estado> colecao_estados;
    colecao_estados.push_back(fechamento_inicial);
    
    // conjunto de todos os simbolos da gramatica
    set<string> simbolos_gramatica;
    for(auto &term: terminais) simbolos_gramatica.insert(term);
    for(auto &nao_term: nao_terminais) simbolos_gramatica.insert(nao_term);

    // algoritmo para construir todos os estados
    bool houve_mudanca = true;
    while(houve_mudanca){
        houve_mudanca = false;
        
        for(size_t i=0; i<colecao_estados.size(); ++i){
            // coleta simbolos que aparecem apos o ponto neste estado
            set<string> simbolos_possiveis;
            for(auto &item: colecao_estados[i]){
                string simb = simbolo_apos_ponto(item, producoes);
                if(!simb.empty()) simbolos_possiveis.insert(simb);
            }
            
            // para cada simbolo, calcula goto e adiciona novo estado se necessario
            for(auto &simbolo: simbolos_possiveis){
                Estado novo_estado = calcular_goto(colecao_estados[i], simbolo, producoes, nao_terminais);
                if(novo_estado.empty()) continue;
                
                if(buscar_indice_estado(colecao_estados, novo_estado) == -1){ 
                    colecao_estados.push_back(novo_estado); 
                    houve_mudanca = true; 
                }
            }
        }
    }

    // constroi as tabelas ACTION e GOTO
    int num_estados = (int)colecao_estados.size();
    
    // tabela ACTION: mapeamento (estado, terminal) -> acao
    vector<unordered_map<string, Acao>> tabela_action(num_estados);
    // tabela GOTO: mapeamento (estado, nao-terminal) -> proximo estado
    vector<unordered_map<string, int>> tabela_goto(num_estados);

    for(int i=0; i<num_estados; ++i){
        for(auto &item: colecao_estados[i]){
            
            if(!ponto_no_final(item, producoes)){
                // caso 1: ponto nao esta no final - pode fazer shift
                string simbolo = simbolo_apos_ponto(item, producoes);
                Estado estado_destino = calcular_goto(colecao_estados[i], simbolo, producoes, nao_terminais);
                
                if(!estado_destino.empty()){
                    int indice_destino = buscar_indice_estado(colecao_estados, estado_destino);
                    
                    if(terminais.count(simbolo)){
                        // simbolo e terminal: adiciona shift
                        Acao acao_shift;
                        acao_shift.tipo = Acao::SHIFT;
                        acao_shift.valor = indice_destino;
                        
                        auto &acao_atual = tabela_action[i][simbolo];
                        if(acao_atual.tipo == Acao::ERRO) {
                            acao_atual = acao_shift;
                        } else if(acao_atual.tipo != acao_shift.tipo || acao_atual.valor != acao_shift.valor){
                            // conflito: prefere shift sobre reduce
                            if(acao_atual.tipo == Acao::REDUCE && acao_shift.tipo == Acao::SHIFT){ 
                                acao_atual = acao_shift; 
                            }
                        }
                    } else if(nao_terminais.count(simbolo)){
                        // simbolo e nao-terminal: adiciona goto
                        tabela_goto[i][simbolo] = indice_destino;
                    }
                }
                
            } else {
                // caso 2: ponto no final - reduce ou accept
                if(item.indice_producao == 0){
                    // producao aumentada S' -> S . => accept no $
                    Acao acao_accept;
                    acao_accept.tipo = Acao::ACCEPT;
                    acao_accept.valor = -1;
                    tabela_action[i]["$"] = acao_accept;
                    
                } else {
                    // reduce por esta producao em todos os terminais (lr(0) simples)
                    Acao acao_reduce;
                    acao_reduce.tipo = Acao::REDUCE;
                    acao_reduce.valor = item.indice_producao;
                    
                    for(auto &terminal: terminais){
                        auto &acao_atual = tabela_action[i][terminal];
                        
                        if(acao_atual.tipo == Acao::ERRO) {
                            acao_atual = acao_reduce;
                        } else if(acao_atual.tipo != acao_reduce.tipo || acao_atual.valor != acao_reduce.valor){
                            // resolucao de conflitos: shift tem prioridade sobre reduce
                            if(acao_atual.tipo == Acao::SHIFT) { 
                                // mantem shift
                            } else if(acao_atual.tipo == Acao::REDUCE){
                                // conflito reduce/reduce: escolhe producao com menor indice
                                if(acao_reduce.valor < acao_atual.valor) 
                                    acao_atual = acao_reduce;
                            }
                        }
                    }
                }
            }
        }
    }

    // exibe resumo da gramatica e automato
    cout<<"producoes da gramatica:\n";
    for(size_t i=0; i<producoes.size(); ++i){
        cout<<"  "<<i<<": "<<producoes[i].lado_esquerdo<<" -> ";
        if(producoes[i].lado_direito.empty()) 
            cout<<"eps";
        else 
            cout<<juntar_strings(producoes[i].lado_direito);
        cout<<"\n";
    }
    
    cout<<"\nestados ("<<num_estados<<"):\n";
    for(int i=0; i<num_estados; ++i){
        cout<<"I"<<i<<":\n";
        for(auto &item: colecao_estados[i]){
            cout<<"  ["<<item.indice_producao<<"] "<<producoes[item.indice_producao].lado_esquerdo<<" -> ";
            
            // exibe o lado direito com o ponto na posicao correta
            for(int k=0; k<(int)producoes[item.indice_producao].lado_direito.size(); ++k){
                if(k == item.posicao_ponto) cout<<". ";
                cout<<producoes[item.indice_producao].lado_direito[k]<<" ";
            }
            if(item.posicao_ponto == (int)producoes[item.indice_producao].lado_direito.size()) 
                cout<<". ";
            cout<<"\n";
        }
        cout<<"\n";
    }

    // exibe tabela ACTION (terminais)
    cout<<"tabela ACTION (terminais):\n";
    vector<string> lista_terminais(terminais.begin(), terminais.end());
    sort(lista_terminais.begin(), lista_terminais.end());
    
    cout<<"estado";
    for(auto &term: lista_terminais) cout<<"\t"<<term;
    cout<<"\n";
    
    for(int i=0; i<num_estados; ++i){
        cout<<i;
        for(auto &term: lista_terminais){
            cout<<"\t";
            auto busca = tabela_action[i].find(term);
            
            if(busca == tabela_action[i].end()) {
                cout<<".";
            } else {
                auto acao = busca->second;
                if(acao.tipo == Acao::SHIFT) 
                    cout<<"s"<<acao.valor;
                else if(acao.tipo == Acao::REDUCE) 
                    cout<<"r"<<acao.valor;
                else if(acao.tipo == Acao::ACCEPT) 
                    cout<<"acc";
                else 
                    cout<<".";
            }
        }
        cout<<"\n";
    }
    cout<<"\ntabela GOTO (nao-terminais):\n";
    vector<string> lista_nao_terminais(nao_terminais.begin(), nao_terminais.end());
    sort(lista_nao_terminais.begin(), lista_nao_terminais.end());
    
    cout<<"estado";
    for(auto &nao_term: lista_nao_terminais) cout<<"\t"<<nao_term;
    cout<<"\n";
    
    for(int i=0; i<num_estados; ++i){
        cout<<i;
        for(auto &nao_term: lista_nao_terminais){
            cout<<"\t";
            auto busca = tabela_goto[i].find(nao_term);
            if(busca == tabela_goto[i].end()) 
                cout<<"."; 
            else 
                cout<<busca->second;
        }
        cout<<"\n";
    }

    // analisa a entrada
    vector<string> tokens_entrada;
    {
        stringstream stream(entrada_string);
        string token;
        while(stream >> token) tokens_entrada.push_back(token);
    }
    tokens_entrada.push_back("$");  // adiciona marcador de fim de entrada

    cout<<"\nanalisando entrada: "<<juntar_strings(tokens_entrada)<<"\n\n";
    
    // pilha de estados do analisador
    vector<int> pilha_estados;
    pilha_estados.push_back(0);  // estado inicial
    size_t indice_entrada = 0;
    
    while(true){
        int estado_topo = pilha_estados.back();
        string token_atual = tokens_entrada[indice_entrada];
        
        // consulta tabela ACTION
        Acao acao = tabela_action[estado_topo].count(token_atual) ? 
                    tabela_action[estado_topo][token_atual] : Acao();
        
        if(acao.tipo == Acao::SHIFT){
            // shift: empilha novo estado e avanca na entrada
            cout<<"shift '"<<token_atual<<"' -> estado "<<acao.valor<<"\n";
            pilha_estados.push_back(acao.valor);
            indice_entrada++;
            
        } else if(acao.tipo == Acao::REDUCE){
            // reduce: aplica producao
            auto &prod = producoes[acao.valor];
            cout<<"reduce pela producao "<<acao.valor<<": "<<prod.lado_esquerdo<<" -> ";
            if(prod.lado_direito.empty()) 
                cout<<"eps"; 
            else 
                cout<<juntar_strings(prod.lado_direito);
            cout<<"\n";
            
            // desempilha estados (um para cada simbolo do lado direito)
            int tamanho_lado_direito = (int)prod.lado_direito.size();
            for(int k=0; k<tamanho_lado_direito; ++k) 
                pilha_estados.pop_back();
            
            // consulta tabela GOTO
            int estado_anterior = pilha_estados.back();
            if(tabela_goto[estado_anterior].count(prod.lado_esquerdo) == 0){ 
                cerr<<"erro: sem GOTO para estado "<<estado_anterior
                    <<" e nao-terminal "<<prod.lado_esquerdo<<"\n"; 
                return 1; 
            }
            int proximo_estado = tabela_goto[estado_anterior][prod.lado_esquerdo];
            pilha_estados.push_back(proximo_estado);
            cout<<"goto estado "<<proximo_estado<<"\n";
            
        } else if(acao.tipo == Acao::ACCEPT){
            cout<<"entrada aceita (ACCEPT)\n";
            break;
            
        } else {
            cerr<<"erro de analise no token '"<<token_atual<<"' (estado "<<estado_topo<<")\n";
            return 1;
        }
    }

    return 0;
}
