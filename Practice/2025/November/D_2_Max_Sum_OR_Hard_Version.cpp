#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 100000;

struct Node{
    vector<int> value = {-1, -1};
    int count;

    Node(){
        count = 0;
    }
};

vector<Node> trie;

void add(int x){
    int v = 0;
    for (int i = 0; i < 30; i++){
        int next = (x >> i) & 1;
        if(trie[v].value[next]==-1){
            trie[v].value[next] = sz(trie);
            trie.emplace_back();
        }
        v = trie[v].value[next];
        trie[v].count++;
    }
}

int get(int x){
    int v = 0, ans = 0;
    for (int i = 0; i < 30; i++){
        int next = !((x >> i) & 1) , child = trie[v].value[next];
        if(child==-1 or trie[child].count==0){
            next ^= 1;
            child = trie[v].value[next];
        }
        ans += (next << i);
        v = child;
        trie[v].count--;
    }
    return ans;
}

void solve()
{
    trie.clear();
    trie.emplace_back();
    int l, r;
    long long ans = 0;
    cin >> l >> r;
    for (int i = l; i <= r; i++){
        add(i);
    }
    vector<int> res;
    for (int i = l; i <= r; i++){
        int p = get(i);
        ans += (i | p);
        res.push_back(p);
    }
    cout << ans << endl;
    for(auto &x: res){
        cout << x << " ";
    }
    cout << endl;
}

int32_t main()
{
    trie.reserve(N);
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}