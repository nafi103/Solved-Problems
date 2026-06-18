#pragma GCC optimize("Ofast")
#include <bits/stdc++.h>
using namespace std;
using ll = long long;
#define int long long
const int MOD = 1000000007;
#define sz(x) (ll)(x).size()
#define rd ({ll x; cin >> x; x; })
#define dbg(x) cerr << "[" #x "]  " << (x) << "\n"
// #define errv(x) {cerr << "["#x"]  ["; for (const auto& ___ : (x)) cerr << ___ << ", "; cerr << "]\n";}
// #define cerr if(0)cerr
#define xx first
#define yy second
mt19937 rnd(std::chrono::high_resolution_clock::now().time_since_epoch().count());
/*_________________________________________________________________________________________________________________________*/
 void Solve()
{
    ll n, k;
    cin >> n >> k;
    vector<pair<ll, ll>> arr(n);
    for (auto& it : arr)
        cin >> it.xx >> it.yy;
    sort(arr.begin(), arr.end());
    ll ans = arr[0].xx;
    ll mxEnd = 0;
    for (int i = 1; i < n; i++) {
        ans = max(ans, arr[i].xx - arr[i - 1].yy);
        mxEnd = max(mxEnd, arr[i - 1].yy);
        arr[i].yy = max(arr[i].yy, mxEnd);
    }
    ans = max(ans, k - arr.back().yy);
    cout << ans << '\n';
}
 int32_t main()
{
    ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
    int t = 1;
    // cin >> t;
    for (int i = 1; i <= t; i++) {
        // cout << "Case #" << i << ": "; // cout << "Case " << i << ": ";
        Solve();
    }
    return 0;
}
// Coded by Tahsin Arafat (@TahsinArafat)