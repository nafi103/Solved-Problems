#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
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
 const int K = 26;
 struct Vertex {
    map<int,int> next;
    int count = 0;
    bool output = false;
     Vertex() {
        next.clear();
    }
};
 struct Trie{
    vector<Vertex> trie;
     Trie(){
        trie = {Vertex()};
    }
     void add_string(string const& s) {
        int v = 0;
        for (char ch : s) {
            int c = ch - 'a';
            if (trie[v].next.count(c) == 0) {
                trie[v].next[c] = trie.size();
                trie.emplace_back();
            }
            v = trie[v].next[c];
            trie[v].count++;
        }
        trie[v].output = true;
    }
     int match(string const &s){
        int v = 0, cnt = 0;
        for (char ch : s) {
            int c = ch - 'a';
            if (trie[v].next.count(c) == 0) {
                break;
            }
            v = trie[v].next[c];
            cnt += trie[v].count;
        }
        return 2 * cnt;
    }
};
 int check(string const &a, int &n){
    int i = 0;
    while(i < n and a[i] == a[n - i - 1]){
        i++;
    }
    return 2 * i;
}
 void solve()
{
    string str, rstr;
    int n;
    cin >> n;
    long long len = 0, ans = 0;
    Trie t_main, t_rev;
    vector<int> fcnt(26, 0), lcnt(26, 0);
    for(int i = 0; i < n; i++){
        cin >> str;
        rstr = str;
        reverse(all(rstr));
        int m = sz(str);
        len += m;
        ans -= t_main.match(rstr);
        ans -= t_rev.match(str);
        ans -= check(str, m);
        t_main.add_string(str);
        t_rev.add_string(rstr);
    }
    ans += 2 * n * len;
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