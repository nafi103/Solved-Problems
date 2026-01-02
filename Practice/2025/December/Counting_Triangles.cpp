#include <bits/stdc++.h>
using namespace std;
#define int long long

const int N = 1e6 + 10;
int n, dp[N], t;

int32_t main()
{
    dp[0] = 0;
    for(int i = 1, flipped = 0; i < N; i++){
        flipped += (i >> 1);
        dp[i] += (i * (i + 1)) / 2 + flipped + dp[i - 1];
    }
    cin >> t;
    while(t--){
        cin >> n;
        cout << dp[n] << '\n';
    }
}