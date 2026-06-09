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
const int N = 2e4;
int spf[N], mu[N], dp[N];
vector<vector<int>> divisors(N);

int nC4(int n){
    if(n < 4)
        return 0;
    return (n * (n - 1) * (n - 2) * (n - 3)) / 24;
}

void solve(){
    for(int i = 0; i < N; i++)
        spf[i] = i;
    for(int i = 2; i * i < N; i++){
        if(spf[i] == i){
            for(int j = i + i; j < N; j += i)
                spf[j] = min(spf[j], i);
        }
    }

    for(int i = 1; i < N; i++){
        for(int j = i; j < N; j += i){
            divisors[j].push_back(i);
        }
    }

    int n;
    while(cin >> n){
        map <int,int> mp;
        for(int i = 0, x; i < n; i++){
            cin >> x;
            for(auto &d: divisors[x])
                mp[d]++;
        }
        for(int i = N - 1; i >= 1; i--){
            dp[i] = nC4(mp[i]);
            for(int j = i + i; j < N; j += i)
                dp[i] -= dp[j];
        }
        cout << dp[1] << endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    for(int i = 0; i < N; i++)
        spf[i] = i;
    for(int i = 2; i * i < N; i++){
        if(spf[i] == i){
            for(int j = i + i; j < N; j += i)
                spf[j] = min(spf[j], i);
        }
    }

    mu[1] = 1;
    for(int i = 2; i < N; i++){
        if((i / spf[i]) % spf[i] == 0)
            mu[i] = 0;
        else
            mu[i] = -mu[i / spf[i]];
    }

    for(int i = 2; i < N; i++){
        for(int j = i; j < N; j += i){
            divisors[j].push_back(i);
        }
    }

    int n;
    while(cin >> n){
        map <int,int> mp;
        for(int i = 0, x; i < n; i++){
            cin >> x;
            if(x > 1)
                for(auto &d: divisors[x])
                    mp[d]++;
        }
        int ans = 0;
        for(auto [f, s]: mp){
            ans += nC4(s) * mu[f];
        }
        cout << nC4(n) + ans << endl;
    }
}