#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int K = 2;

struct Vertex {
    int next[K];

    Vertex() {
        fill(begin(next), end(next), -1);
    }
};

vector<Vertex> trie(1);

void add(const int& num) {
    int v = 0;
    for (int i = 29; i >= 0; i--) {
        int c = ((1 << i) & num) > 0;
        if (trie[v].next[c] == -1) {
            trie[v].next[c] = trie.size();
            trie.emplace_back();
        }
        v = trie[v].next[c];
    }
}

int query(const int& num){
    int v = 0, mx = 0;
    for(int i = 29; i >= 0; i--){
        int c = ((1 << i) & num) > 0;
        c = c ^ 1;
        if(trie[v].next[c] == -1){
            c = c ^ 1;
        }else{
            mx |= (1 << i);
        }
        v = trie[v].next[c];
    }
    return mx;
}

void solve()
{
    int n;
    cin >> n;
    int arr[n];
    int ans = 0;
    add(ans);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        if(i)
            arr[i] = (arr[i] ^ arr[i - 1]);
        ans = max(ans, query(arr[i]));
        add(arr[i]);
    }
    cout << ans << endl;
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