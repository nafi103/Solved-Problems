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
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
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
    int next[K];
    int pref_count = 0, output = 0;
    string max_string = "{";

    Vertex() {
        fill(begin(next), end(next), -1);
    }
};

vector<Vertex> Trie(1);

void add_string(string const& s) {
    int v = 0;
    vector<int>parents;
    for (char ch : s) {
        int c = ch - 'a';
        if (Trie[v].next[c] == -1) {
            Trie[v].next[c] = Trie.size();
            Trie.emplace_back();
        }
        v = Trie[v].next[c];
        parents.push_back(v);
    }
    Trie[v].output++;
    int e = Trie[v].output;
    for(auto &x: parents){
        if(Trie[x].pref_count<e){
            Trie[x].pref_count = e;
            Trie[x].max_string = s;
        }else if(Trie[x].pref_count==e){
            Trie[x].max_string = min(Trie[x].max_string,s);
        }
    }
}

pair<string,int> find_occurance(string const &s){
    int v = 0;
    for (char ch : s) {
        int c = ch - 'a';
        if (Trie[v].next[c] == -1) {
            Trie[v].next[c] = Trie.size();
            Trie.emplace_back();
        }
        v = Trie[v].next[c];
    }
    return {Trie[v].max_string,Trie[v].pref_count};
}

void solve()
{
    string str;
    int n,q;
    cin>>n;
    while(n--){
        cin>>str;
        add_string(str);
    }
    cin>>q;
    while(q--){
        cin>>str;
        pair<string,int> ans = find_occurance(str);
        if(ans.second==0){
            cout<<-1<<endl;
        }else{
            cout<<ans.first<<" "<<ans.second<<endl;
        }
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
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}