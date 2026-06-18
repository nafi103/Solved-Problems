#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
const int inf = 1e18 + 10;
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
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);} 
 void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> v(n + 1, 0), hash(n + 1, 0);
    map<int, int> mp;
    for (int i = 1; i <= n; i++){
        cin >> v[i];
        if(mp.count(v[i]) == 0){
            mp[v[i]] = getRandomNumber(1, inf);
        }
        hash[i] = mp[v[i]];
        v[i] = (v[i] ^ v[i - 1]);
        hash[i] = (hash[i] ^ hash[i - 1]);
    }
    while(q--){
        int l, r;
        cin >> l >> r;
        l--;
        if((r - l)%2 == 0 and (v[r] ^ v[l]) == 0 and (hash[r] ^ hash[l]) == 0){
            cout << "YES" << endl;
        }else{
            cout << "NO" << endl;
        }
    }
}
 int32_t main()
{
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