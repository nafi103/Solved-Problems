#include <bits/stdc++.h>
using namespace std;
int main()
{
    int n;
    cin >> n;
    for(int i=n;i>=1;i--)
    {
        for(int j=1;j<=2*n-2*i;j++)
        {
            cout<<" ";
        }
        for(int k=1;k<=2*i-1;k++)
        {
            cout<<"*";
            if(k!=2*i-1)
            {
                cout<<" ";
            }
        }
        cout<<endl;
    }
}