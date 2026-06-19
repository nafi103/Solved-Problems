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

const int N = 80;
vector<vector<int>> divisors(N);

void solve()
{
    int n, ans = 0;
    cin >> n;

    if(n <= 2){
        cout << 0 << endl;
        return;
    }

    for(int b = 2, np, g, cnt, last = -1, r; b * b <= n; b++){ // Need to optimize this
        np = n; g = 0; cnt = 0; last = -1;
        while(np){
            r = np % b;
            if(r != last){
                g = gcd(g, cnt);
                cnt = 0;
            }
            np /= b;
            cnt++;
            last = r;
        }

        g = gcd(g, cnt);
        if(g > 1)
            ans += sz(divisors[g]);
    }

    for(int r = 1; r * r <= n; r++){  // sqrt(n)
        int nn = n - r;

        if(nn % r != 0)
            continue;

        int b = nn / r;

        if(b > r)
            ans++;
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

    for(int i = 2; i < N; i++){
        for(int j = i; j < N; j += i){
            divisors[j].push_back(i);
        }
        reverse(all(divisors[i]));
    }

    // debug(divisors)

    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}