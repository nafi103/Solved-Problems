#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
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

const int N = 20;
int fact[N];

void precalculate(){
    fact[0] = 1;
    for(int i = 1; i < N; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
}

vector<int> get_divisors(int n){
    vector<int> d;
    for(int i = 1; i * i <= n; i++){
        if(n % i == 0){
            d.push_back(i);
            if(n / i != i)
                d.push_back(n / i);
        }
    }

    sort(all(d));
    return d;
}

void solve()
{
    int n;
    cin >> n;
    vector<int> divisors = get_divisors(n);
    sort(all(divisors));

    auto get_id = [&](int num){
        return lower_bound(all(divisors), num) - divisors.begin();
    };

    int k = sz(divisors);
    vector<vector<int>> dp0(15, vector<int> (k, 0)); //number of ways
    vector<vector<int>> dp1 = dp0; // sum of ways

    dp0[0][0] = 1;
    for(int i = 0; i < k; i++){
        int d = divisors[i], dm = d % mod;

        for(int j = k - 1; j >= 0; j--){
            if((n / divisors[j]) % d == 0){
                int nxt = get_id(divisors[j] * d);

                for(int s = 13; s >= 0; s--){
                    if(dp0[s][j] == 0)
                        continue;

                    dp0[s + 1][nxt] = (dp0[s + 1][nxt] + dp0[s][j]) % mod;
                    int add = dp0[s][j] * dm;
                    dp1[s + 1][nxt] = (dp1[s + 1][nxt] + dp1[s][j] + add) % mod;
                }
            }
        }
    }

    int ans = 0;
    for(int s = 1; s <= 14; s++){
        ans = (ans + dp1[s][k - 1] * fact[s]) % mod;
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
    precalculate();
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}