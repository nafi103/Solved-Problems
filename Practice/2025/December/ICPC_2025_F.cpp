#include <bits/stdc++.h>
using namespace std;
#define ll int64_t
#define int int64_t
const int MOD = 1e9+7;
const int inf = 1e18;
#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define sz(x) (int)(x).size()
auto rd = [](){ll x;cin>>x;return x;};
#define dbg(x) cerr<<"["#x"]"<<(x)<<"\n"
mt19937_64 rnd((unsigned int)chrono::steady_clock::now().time_since_epoch().count());

bool check(int target, int &len, int &v, int &t){
    return target * len <= t * v;
}

int bs(int l, int r, int &len, int &v, int &t){
    if(l > r)
        return r;
    int mid = ( l + r) / 2;
    if(check(mid, len, v, t))
        return bs(mid + 1, r, len, v, t);
    return bs(l, mid - 1, len, v, t);
}

void solve() {
    int L, ini, T, n;
    cin >> L >> ini >> T >> n;
    while(n--){
        int v,t;
        cin >> t >> v;
        int vt = abs(v - ini);
        int rt = (T - t);
        cout << 1 + bs(0, 1e12, L, vt, rt) << (n > 0 ? ' ' : '\n');
    }
}

int32_t main() {
    ios_base::sync_with_stdio(0), cin.tie(nullptr), cout.tie(nullptr);
    int t = 1;
    cin >> t;
    for (int cs = 1; cs <= t; ++cs) {
        // cout << "Case " << cs << ": ";
        solve();
    }
    return 0;
}