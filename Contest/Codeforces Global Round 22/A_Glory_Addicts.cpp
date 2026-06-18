#include <bits/stdc++.h>
#define ll long long
using namespace std;
 void solution()
{
    vector<ll> v1, v0;
    ll n, dmg = 0, zcnt = 0, ocnt = 0, mn = INT_MAX;
    cin >> n;
    ll arr1[n], arr2[n];
    for (ll i = 0; i < n; i++)
    {
        cin >> arr1[i];
        if (arr1[i] == 1)
        {
            ocnt++;
        }
        else
        {
            zcnt++;
        }
    }
    for (ll i = 0; i < n; i++)
    {
        cin >> arr2[i];
        if (mn > arr2[i])
            mn = arr2[i];
        if (arr1[i] == 1)
        {
            v1.push_back(arr2[i]);
        }
        else
        {
            v0.push_back(arr2[i]);
        }
    }
    sort(v0.rbegin(), v0.rend());
    sort(v1.rbegin(), v1.rend());
    int sml = min(zcnt, ocnt);
    for (int i = 0; i < sml; i++)
    {
        dmg += 2 * v0[i];
    }
    for (int i = sml; i < v0.size(); i++)
    {
        dmg += v0[i];
    }
    for (int i = 0; i < sml; i++)
    {
        dmg += 2 * v1[i];
    }
    for (int i = sml; i < v1.size(); i++)
    {
        dmg += v1[i];
    }
    if (ocnt == zcnt)
        dmg -= mn;
    cout << dmg << endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}