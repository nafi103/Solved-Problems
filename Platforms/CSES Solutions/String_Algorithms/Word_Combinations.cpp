#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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
    int next[K];
    bool output = false;

    Vertex() {
        fill(begin(next), end(next), -1);
    }
};

vector<Vertex> Trie(1);

void add_string(string const& s) {
    int v = 0;
    for (char ch : s) {
        int c = ch - 'a';
        if (Trie[v].next[c] == -1) {
            Trie[v].next[c] = Trie.size();
            Trie.emplace_back();
        }
        v = Trie[v].next[c];
    }
    Trie[v].output = true;
}

void delete_string(string const& s) {
    int v = 0;
    for (char ch : s) {
        int c = ch - 'a';
        if (Trie[v].next[c] == -1) {
            return;
        }
        v = Trie[v].next[c];
    }
    Trie[v].output = false;
}

string str;
vector<int>dp;

int f(int pos){
    if(pos==sz(str))
        return 1;
    int &ans = dp[pos], v = 0;
    if(ans!=-1)
        return ans;
    ans = 0;
    for(int i = pos; i<sz(str); i++){
        int c = str[i] - 'a';
        if(Trie[v].next[c]==-1)
            break;
        v = Trie[v].next[c];
        if(Trie[v].output)
            ans = (ans+f(i+1))%mod;
    }
    return ans;
}

void solve()
{
    cin>>str;
    int n;
    cin>>n;
    while(n--){
        string tmp;
        cin>>tmp;
        add_string(tmp);
    }
    dp.assign(sz(str),-1);
    cout<<f(0)<<endl;
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