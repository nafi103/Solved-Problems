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

const int K = 10;

struct Vertex {
    char c = '$';
    int next[K], len[20];
    bool output = false;

    Vertex() {
        fill(begin(next), end(next), -1);
        fill(begin(len), end(len), 0);
    }
};

vector<Vertex> Trie(1);
vector<int>seq(10),mp(10);

void add_string(string const& s) {
    int v = 0, l = sz(s);
    Trie[0].len[l]++;
    for (char ch : s) {
        int c = ch - '0';
        if (Trie[v].next[c] == -1) {
            Trie[v].next[c] = Trie.size();
            Trie.emplace_back();
        }
        v = Trie[v].next[c];
        Trie[v].c = ch;
        Trie[v].len[--l]++;
    }
    Trie[v].output = true;
}

int get_ans(string &str, int pos, int node){
    if(pos==sz(str)-1){
        if(mp[str[pos]-'0']>mp[Trie[node].c-'0'])
            Trie[node].len[0];
        else
            return 0;
    }
    if(str[pos]!=Trie[node].c)
        return Trie[node].len[sz(str)-pos-1];
    int t = str[pos+1]-'0', ans = 0;
    for(int i = 0; i<10; i++){
        if(Trie[node].next[seq[i]]!=-1)
            ans+=get_ans(str,pos+1,Trie[node].next[seq[i]]);
        if(seq[i]==t)
            break;
    }
    return ans;
}

void solve()
{
    int n;
    cin>>n;
    string str;
    while(n--){
        cin>>str;
        add_string(str);
    }
    int q;
    cin>>q;
    while(q--){
        for(int i = 0; i<10; i++){
            auto &x = seq[i];
            cin>>x;
            mp[x] = i;
        }
        cin>>str;
        int ans = 0, l = sz(str);
        for(int i = 1; i<l; i++)
            ans+=Trie[0].len[i];
        for(int i = 0; i<10; i++){
            if(Trie[0].next[seq[i]]!=-1)
                ans+=get_ans(str,0,Trie[0].next[seq[i]]);
            if(seq[i]==str[0]-'0')
                break;
        }
        cout<<ans<<endl;
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