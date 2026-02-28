#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int K = 26, Null = -1, none = -2;

struct Node{
    vector<int> next, go, output;
    int link, output_link;

    Node(){
        next.assign(K, Null);
        go.assign(K, Null);
        output.clear();
        link = output_link = Null;
    }
};

vector<Node> trie(1);

void add_string(string &str, int &id){
    int node = 0;
    for(char &ch: str){
        int c = ch - 'a';
        if(trie[node].next[c] == -1){
            trie[node].next[c] = sz(trie);
            trie.emplace_back();
        }
        node = trie[node].next[c];
    }
    trie[node].output.push_back(id);
}

void add_links(){
    trie[0].output_link = none;
    queue<int> q;

    for(int c = 0; c < K; c++){
        if(trie[0].next[c] != Null){
            int v = trie[0].next[c];
            trie[0].go[c] = v;
            trie[v].output_link = none;
            trie[v].link = 0;
            q.push(v);
        }else{
            trie[0].go[c] = 0;
        }
    }

    while(!q.empty()){
        int node = q.front();
        q.pop();
        for(int c = 0; c < K; c++){
            int v = trie[node].next[c], suffix_link = trie[node].link;
            if(v != Null){
                while(suffix_link != 0 and trie[suffix_link].next[c] == Null)
                    suffix_link = trie[suffix_link].link;
                int suffix_child = trie[suffix_link].next[c];
                if(suffix_child != Null){
                    trie[v].link = suffix_child;
                    if(!trie[suffix_child].output.empty())
                        trie[v].output_link = suffix_child;
                    else
                        trie[v].output_link = trie[suffix_child].output_link;
                }else{
                    trie[v].output_link = none;
                    trie[v].link = 0; 
                }
                q.push(v);
            }
            trie[node].go[c] = (v != Null) ? v : trie[suffix_link].go[c];
        }
    }
}

void pull_answer(int node, int i, vector<int> &ans, vector<int> &len){
    vector<int> &output = trie[node].output;
    while(!output.empty()){
        int id = output.back();
        output.pop_back();
        ans[id] = i - len[id] + 1;
    }
    if(trie[node].output_link != none)
        pull_answer(trie[node].output_link, i, ans, len);
    trie[node].output_link = none;
}

void solve()
{
    string text, str;
    cin >> text;
    int n;
    cin >> n;
    vector<int> len(n), ans(n, -1);
    for(int i = 0; i < n; i++){
        cin >> str;
        len[i] = sz(str);
        add_string(str, i);
    }
    add_links();
    for(int i = 0, node = 0; i < sz(text); i++){
        int c = text[i] - 'a';
        node = trie[node].go[c];
        pull_answer(node, i + 1, ans, len);
    }
    for(auto &x: ans)
        cout << x << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}