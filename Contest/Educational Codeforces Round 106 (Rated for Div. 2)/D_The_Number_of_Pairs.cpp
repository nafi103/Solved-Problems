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
 const int N = 2e7;
vector<int> spf(N + 1), distinct_prime(N + 1);
vector<int> pr;
 pair<int,int> get_pair(int a, int b, int c, int y){
    int nom = c / y + b;
    if(nom < a or nom % a != 0)
        return {-1, -1};
    int k = nom / a;
    return {k * y, y};
}
 void solve()
{
    int a, b, c, x, y, g, ans = 0;
    cin >> a >> b >> c;
    if(c % gcd(a, b) != 0){
        cout << 0 << endl;
        return;
    }
    for(int y = 1; y * y <= c; y++){
        if(c % y == 0){
            auto [l, g] = get_pair(a, b, c, y);
            if(l != -1){
                int rem = l / g, prev = -1;
                ans += (1 << distinct_prime[rem]);
            }
            if(y * y != c){
                tie(l, g) = get_pair(a, b, c, c / y);
                if(l != -1){
                    int rem = l / g, prev = -1;
                    ans += (1 << distinct_prime[rem]);
                }
            }
        }
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
     for (int i=2; i <= N; ++i) {
        if (spf[i] == 0) {
            spf[i] = i;
            pr.push_back(i);
        }
        for (int j = 0; i * pr[j] <= N; ++j) {
            spf[i * pr[j]] = pr[j];
            if (pr[j] == spf[i]) {
                break;
            }
        }
    }
    for(auto &p: pr){
        for(int i = p; i <= N; i += p){
            distinct_prime[i]++;
        }
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}