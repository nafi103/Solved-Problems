#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

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
const int K = 2;

struct Vertex {
    int next[K];
    int through = 0;

    Vertex() {
        fill(begin(next), end(next), -1);
    }
};

vector<Vertex> Trie(1);

void add_string(int num) {
    int v = 0;
    vector<int>s;
    for(int i = 29, j = 1<<29; i>=0; i--, j>>=1){
        s.push_back((num&j)!=0);
    }
    for (int c : s) {
        if (Trie[v].next[c] == -1) {
            Trie[v].next[c] = Trie.size();
            Trie.emplace_back();
        }
        v = Trie[v].next[c];
        Trie[v].through++;
    }
}

void delete_string(int num) {
    int v = 0;
    vector<int>s;
    for(int i = 29, j = 1<<29; i>=0; i--, j>>=1){
        s.push_back((num&j)!=0);
    }
    for (int c : s) {
        if (Trie[v].next[c] == -1) {
            return;
        }
        v = Trie[v].next[c];
        Trie[v].through--;
    }
}

int get_ans(int num){
    int v = 0, ans = 0, curr_bit = (1<<29);
    vector<int>s;
    for(int i = 29, j = 1<<29; i>=0; i--, j>>=1){
        s.push_back((num&j)!=0);
    }
    for (int c : s) {
        int cp = (c^1);
        if (Trie[v].next[cp] != -1 and Trie[Trie[v].next[cp]].through) {
            ans+=curr_bit;
            v = Trie[v].next[cp];
        }else{
            v = Trie[v].next[c];
        }
        curr_bit>>=1;
    }
    return ans;
}

void solve()
{
    add_string(0);
    char t;
    int q,n;
    cin>>q;
    while(q--){
        cin>>t>>n;
        if(t=='+'){
            add_string(n);
        }else if(t=='-'){
            delete_string(n);
        }else{
            cout<<get_ans(n)<<endl;
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