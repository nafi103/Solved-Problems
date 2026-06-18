#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int K = 26;

struct Vertex {
    vector<int>next_char, go;
    bool output = false;
    int link = -1;
    int end_index = -1;

    Vertex(){
        next_char.assign(K,-1);
        go.assign(K,-1);
    }
};

vector<Vertex> Trie(1);
vector<int>ans_index;
vector<bool>ans;

void add_string(string const& s, int &end_index) {
    int v = 0;
    for (char ch : s) {
        int c = ch - 'a';
        if (Trie[v].next_char[c] == -1) {
            Trie[v].next_char[c] = Trie.size();
            Trie.emplace_back();
        }
        v = Trie[v].next_char[c];
    }
    if(!Trie[v].output)
        Trie[v].end_index = end_index;
    else
        ans_index[end_index] = Trie[v].end_index;
    Trie[v].output = true;
}

void add_links() {
    queue<int> q;
    Trie[0].link = 0;
    for (int c = 0; c < K; c++) {
        int u = Trie[0].next_char[c];
        if (u != -1) {
            Trie[u].link = 0;
            q.push(u);
            Trie[0].go[c] = u;
        } else {
            Trie[0].go[c] = 0;
        }
    }
    while (!q.empty()) {
        int u = q.front(); 
        q.pop();
        for (int c = 0; c < K; c++) {
            int v = Trie[u].next_char[c], suffix_link = Trie[u].link;
            if (v != -1) {

                while (suffix_link != 0 && Trie[suffix_link].next_char[c] == -1){
                    suffix_link = Trie[suffix_link].link;
                }

                if (Trie[suffix_link].next_char[c] != -1)
                    Trie[v].link = Trie[suffix_link].next_char[c];
                else
                    Trie[v].link = 0;

                q.push(v);
            }
            Trie[u].go[c] = (v != -1) ? v : Trie[suffix_link].go[c];
        }
    }
}

void solve()
{
    int m;
    string str;
    cin>>str>>m;
    int n = sz(str);
    ans_index.resize(m);
    ans.assign(m,false);
    for(int i = 0; i<m; i++)
        ans_index[i] = i;
    vector<string> words(m);
    readv(words);
    for(int i = 0; i<m; i++){
        add_string(words[i],i);
    }
    add_links();
    int curr = 0;
    vector<bool>visited(sz(Trie),false);
    visited[0] = true;
    for(int i = 0; i<n; i++){
        curr = Trie[curr].go[str[i]-'a'];
        visited[curr] = true;
        if(Trie[curr].output and Trie[curr].end_index>=0)
            ans[Trie[curr].end_index] = true;
        int link = Trie[curr].link;
        while (link>0 and !visited[link])
        {
            visited[link] = true;
            if (Trie[link].output and Trie[link].end_index>=0){
                ans[Trie[link].end_index] = true;
            }
            link = Trie[link].link;
        }
    }
    for(int i = 0; i<m; i++){
        if(ans[ans_index[i]])
            yes;
        else
            no;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}